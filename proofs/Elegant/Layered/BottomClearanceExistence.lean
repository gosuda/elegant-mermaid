import Elegant.Layered.BottomClearanceClosure
import Elegant.Layered.FrameClearanceBottomFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

/-- Candidate bottom marker existence: every group top marker of the measured graph whose
graph index lies in `comp` has its paired bottom marker (`border = 2`, same `decl`) present
in the candidate graph's node list, found by the same predicate `Compound.constraints` uses. -/
def CandidateBottomExists {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hgraph : measuredGraph P inp o lines = .ok graph)
    (_hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (_hcomp : comp ∈ components graph) (candidate : Nat) : Prop :=
  ∀ top : Node × Nat, top ∈ graph.nodes.zipIdx → top.2 ∈ comp → top.1.border = -2 →
    ∃ bottom : Node × Nat,
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom

/-- Candidate parent top existence: a candidate group top whose cluster path has a strict
nonempty prefix has its parent group top marker (the `border = -2` node whose cluster path
is the child's `dropLast`) present in the same candidate graph.  `framedParents` rules out
fixed-size demotion of the parent box, which would remove its top marker entirely. -/
def CandidateParentTopExists {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hgraph : measuredGraph P inp o lines = .ok graph)
    (_hlines : lines.length = inp.boxes.length)
    (_hwf : WellFormed (inputModel inp o))
    (_hframed : framedParents inp = true)
    {comp : List Nat} (_hcomp : comp ∈ components graph) (candidate : Nat) : Prop :=
  ∀ x : Node × Nat, x ∈ (componentCandidate graph comp candidate).nodes.zipIdx →
    x.1.border = -2 →
    ∀ outerPrefix : List Nat, outerPrefix <+: x.1.clusterPath →
      outerPrefix.length < x.1.clusterPath.length → outerPrefix ≠ [] →
      ∃ parent : Node × Nat,
        (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
          entry.1.border == -2 && entry.1.clusterPath == x.1.clusterPath.dropLast) =
            some parent

/-! ### Shared helpers

The two existence units share one connectivity bridge: an edge of the measured graph or of
its compound constraints keeps both endpoints inside any component already containing one
of them. -/

private theorem measuredConstraintsBounded {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hgraph : measuredGraph P inp o lines = .ok g)
    (hlines : lines.length = inp.boxes.length) :
    ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact measuredGraph_edges_bounded hgraph hlines e he
  · exact constraints_bounded g e he

private theorem pushIntoComp {graph : Graph} {comp : List Nat}
    (hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length)
    (hcompMem : comp ∈ components graph)
    {e : Edge} (he : e ∈ graph.edges ++ Compound.constraints graph)
    (hta : e.tail ∈ comp) : e.head ∈ comp := by
  obtain ⟨c, hcMem, hca, hcb⟩ := components_edge_endpoints hbd he
  have heq : c = comp := components_shared_member_eq hcMem hcompMem hca hta
  rw [heq] at hcb
  exact hcb

private theorem findSomeOfMember {l : List (Node × Nat)} {pred : Node × Nat → Bool}
    {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

/-- Every measured-graph group top finds its paired bottom marker by declaration. -/
private theorem groupTopFind?_some {P : Params} {inp : Input} {o : Options}
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
  exact findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hidx) hp

/-- Inverting a fixed-boxes lookup recovers the original box, its id and parent, and the
fact that a surviving group box was never demoted. -/
private theorem demote_lookup {inp : Input} {i : Nat} {b : ModelBox}
    (h : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box)[i]? = some b) :
    ∃ orig : ModelBox, inp.boxes[i]? = some orig ∧ b.id = orig.id ∧ b.parent = orig.parent ∧
      (b.role = .group →
        ¬(inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id) = true)) ∧
      b = (if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id) then
            { orig with role := .node } else orig) := by
  rw [List.getElem?_map] at h
  cases hop : inp.boxes[i]? with
  | none => rw [hop] at h; simp at h
  | some orig =>
    rw [hop, Option.map_some, Option.some.injEq] at h
    by_cases hfixed : inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id)
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

private theorem demote_id {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

private theorem demote_parent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

private theorem demote_length {inp : Input} :
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box).length ≤ inp.boxes.length := by
  rw [List.length_map]
  exact Nat.le_refl _

/-! ### Unit A: the paired bottom marker is in the component -/

theorem candidate_group_bottom_find {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat) :
    CandidateBottomExists hgraph hlines hcomp candidate := by
  unfold CandidateBottomExists
  have hbd := measuredConstraintsBounded hgraph hlines
  have key : ∀ fuel : Nat, ∀ t : Node × Nat, t ∈ graph.nodes.zipIdx →
      t.1.border = -2 →
      t.1.clusterPath.length ≤ inp.boxes.length + 1 →
      inp.boxes.length + 2 - t.1.clusterPath.length < fuel →
      ∃ gb : Node × Nat,
        graph.nodes.zipIdx.find? (fun e =>
          e.1.border == 2 && e.1.decl == t.1.decl) = some gb ∧
        ∀ c ∈ components graph, t.2 ∈ c → gb.2 ∈ c := by
    intro fuel
    induction fuel with
    | zero =>
      intro t htop hgroup _ hmeas
      exact absurd hmeas (Nat.not_lt_zero _)
    | succ fuel ih =>
      intro t htop hgroup hpathBound hmeas
      obtain ⟨gb, hfind⟩ := groupTopFind?_some hgraph hlines htop hgroup
      refine ⟨gb, hfind, ?_⟩
      intro c hcMem htinc
      by_cases hmemEmpty : (graph.nodes.zipIdx.filter (fun q =>
          q.1.border == 0 && q.1.clusterPath.contains t.1.decl)).isEmpty = true
      · by_cases hchildEmpty : ((graph.nodes.zipIdx.filter fun q =>
            q.1.border == -2).filter
            fun q => q.1.clusterPath.dropLast == t.1.clusterPath).isEmpty = true
        · have hdirect := compound_empty_group_constraint_edge htop hgroup hfind
            hmemEmpty hchildEmpty
          have h := pushIntoComp hbd hcMem (List.mem_append_right _ hdirect) htinc
          simpa using h
        · -- members empty, children nonempty: route through the child's bottom
          have hchildNE : ∃ child : Node × Nat,
              child ∈ ((graph.nodes.zipIdx.filter fun q => q.1.border == -2).filter
                fun q => q.1.clusterPath.dropLast == t.1.clusterPath) := by
            cases hl : ((graph.nodes.zipIdx.filter fun q => q.1.border == -2).filter
                fun q => q.1.clusterPath.dropLast == t.1.clusterPath) with
            | nil => rw [hl] at hchildEmpty; exact absurd rfl hchildEmpty
            | cons first rest => exact ⟨first, by simp⟩
          obtain ⟨child, hchild⟩ := hchildNE
          obtain ⟨hchildTops, hchildPathEq⟩ := List.mem_filter.mp hchild
          obtain ⟨hchildZip, hchildBorderBeq⟩ := List.mem_filter.mp hchildTops
          have hchildBorder : child.1.border = -2 := by simpa using hchildBorderBeq
          have hchildPath : child.1.clusterPath.dropLast = t.1.clusterPath := by
            simpa using hchildPathEq
          have hchildLookup : graph.nodes[child.2]? = some child.1 :=
            List.mem_zipIdx_iff_getElem?.mp hchildZip
          have hchildNe := ((measuredGraph_marker_shape hgraph hchildLookup).2 hchildBorder)
          have hchildLen : child.1.clusterPath.length = t.1.clusterPath.length + 1 := by
            have h1 : child.1.clusterPath.dropLast.length =
                child.1.clusterPath.length - 1 := List.length_dropLast ..
            rw [hchildPath] at h1
            have hge : 1 ≤ child.1.clusterPath.length :=
              Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun h =>
                hchildNe (List.length_eq_zero_iff.mp h))
            have hshift : child.1.clusterPath.length - 1 + 1 =
                child.1.clusterPath.length := Nat.sub_add_cancel hge
            rw [← hshift, h1]
          have hchildPathBound : child.1.clusterPath.length ≤ inp.boxes.length + 1 := by
            obtain ⟨_, cbox, _, _, hchildPathOrigin⟩ :=
              measuredGraph_group_origin hgraph hchildLookup hchildBorder
            rw [hchildPathOrigin, List.length_append, List.length_singleton]
            simp only [Compound.path]
            have h := ancestors_length_le
              (inp.boxes.map fun box =>
                if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
                  { box with role := .node } else box)
              (inp.boxes.map fun box =>
                if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
                  { box with role := .node } else box).length cbox.parent
            exact Nat.succ_le_succ (Nat.le_trans h demote_length)
          have hchildBound : inp.boxes.length + 2 - child.1.clusterPath.length < fuel := by
            omega
          obtain ⟨cb, hcbfind, hcbprop⟩ := ih child hchildZip hchildBorder
            hchildPathBound hchildBound
          obtain ⟨he₁, he₂⟩ := compound_child_constraint_edges htop hgroup hfind
            hchildZip hchildBorder hchildPath hcbfind
          have hchildIn : child.2 ∈ c :=
            pushIntoComp hbd hcMem (List.mem_append_right _ he₁) htinc
          have hcbIn : cb.2 ∈ c := hcbprop c hcMem hchildIn
          have h := pushIntoComp hbd hcMem (List.mem_append_right _ he₂) hcbIn
          simpa using h
      · -- members nonempty: route through the first member
        have hmemNE : ∃ m : Node × Nat, m ∈ graph.nodes.zipIdx.filter (fun q =>
            q.1.border == 0 && q.1.clusterPath.contains t.1.decl) := by
          cases hl : (graph.nodes.zipIdx.filter (fun q =>
              q.1.border == 0 && q.1.clusterPath.contains t.1.decl)) with
          | nil => rw [hl] at hmemEmpty; exact absurd rfl hmemEmpty
          | cons first rest => exact ⟨first, by simp⟩
        obtain ⟨member, hmember⟩ := hmemNE
        obtain ⟨hmZip, hmPred⟩ := List.mem_filter.mp hmember
        obtain ⟨hbeqBorder, hinside⟩ := Bool.and_eq_true_iff.mp hmPred
        have hmPlain : member.1.border = 0 := by simpa using hbeqBorder
        obtain ⟨he₁, he₂⟩ := compound_member_constraint_edges htop hgroup hfind
          hmZip hmPlain hinside
        have hmemberIn : member.2 ∈ c :=
          pushIntoComp hbd hcMem (List.mem_append_right _ he₁) htinc
        have h := pushIntoComp hbd hcMem (List.mem_append_right _ he₂) hmemberIn
        simpa using h
  intro top hmem htopinc hgroup
  have hlookup : graph.nodes[top.2]? = some top.1 := List.mem_zipIdx_iff_getElem?.mp hmem
  obtain ⟨hdecl, box, hbox, _, hpath⟩ := measuredGraph_group_origin hgraph hlookup hgroup
  have hplen : (Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box).length ≤
      inp.boxes.length := by
    unfold Compound.path
    refine Nat.le_trans (ancestors_length_le _ _ _) ?_
    rw [List.length_map]
    exact Nat.le_refl _
  have hlen : top.1.clusterPath.length ≤ inp.boxes.length + 1 := by
    rw [hpath]
    simp only [List.length_append, List.length_singleton]
    omega
  have htopPos : 0 < top.1.clusterPath.length :=
    Nat.pos_of_ne_zero fun h =>
      ((measuredGraph_marker_shape hgraph hlookup).2 hgroup) (List.length_eq_zero_iff.mp h)
  obtain ⟨gb, hfind, hprop⟩ := key (inp.boxes.length + 2) top hmem hgroup hlen (by omega)
  have hgbFacts : gb.1.border = 2 ∧ gb.1.decl = top.1.decl := by
    have hp : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == top.1.decl) gb) = true :=
      List.find?_some (p := fun e : Node × Nat =>
        e.1.border == 2 && e.1.decl == top.1.decl) hfind
    simpa using hp
  have hgbIn : gb.2 ∈ comp := hprop comp hcomp htopinc
  have hlookupGb : graph.nodes[gb.2]? = some gb.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
  have hgb1in : gb.1 ∈ (componentCandidate graph comp candidate).nodes := by
    rw [componentCandidate_nodes]
    exact List.mem_map.mpr ⟨gb.2, hgbIn, by
      rw [List.getD_eq_getElem?_getD, hlookupGb]
      rfl⟩
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp hgb1in
  have hp : ((fun entry : Node × Nat =>
      entry.1.border == 2 && entry.1.decl == top.1.decl) (gb.1, i₀)) = true := by
    simp [hgbFacts.1, hgbFacts.2]
  exact findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hi₀) hp

/-! ### Unit B: the parent group top marker is in the component -/

theorem candidate_parent_top_exists {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat) :
    CandidateParentTopExists hgraph hlines hwf hframed hcomp candidate := by
  unfold CandidateParentTopExists
  intro x hxMem hxGroup outerPrefix hpre hlen hne
  have hbd := measuredConstraintsBounded hgraph hlines
  have hzipLookup : (componentCandidate graph comp candidate).nodes[x.2]? = some x.1 :=
    List.mem_zipIdx_iff_getElem?.mp hxMem
  obtain ⟨oIdx, ho, hsource⟩ := componentCandidate_nonplain_source hzipLookup (by omega)
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? ho
  obtain ⟨hxdecl, box_x, hboxx, hrolex, hxpath⟩ :=
    measuredGraph_group_origin hgraph hsource hxGroup
  obtain ⟨orig_x, horigLookup, hidx, hparentOf, hnotfixed, hdemoteX⟩ :=
    demote_lookup hboxx
  have hpathXNe : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box_x ≠ [] := by
    intro hnil
    have hclen : x.1.clusterPath.length = 1 := by rw [hxpath, hnil]; simp
    have hoplen : outerPrefix.length = 0 := by omega
    have hopnil : outerPrefix = [] := List.length_eq_zero_iff.mp hoplen
    exact hne hopnil
  have hdrop : x.1.clusterPath.dropLast = Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box_x := by
    rw [hxpath, List.dropLast_append_of_ne_nil (l := [x.1.decl]) (by simp)]
    simp
  have hnf : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == orig_x.id) = true) := hnotfixed hrolex
  have hbxOrig : box_x = orig_x := by rw [hdemoteX, ite_eq_right hnf]
  rw [hbxOrig] at hdrop hpathXNe
  have hpxne : orig_x.parent ≠ "" := by
    intro hempty
    refine hpathXNe ?_
    unfold Compound.path
    rw [hempty]
    cases hlen : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box).length with
    | zero => simp [Compound.ancestors]
    | succ n => simp [Compound.ancestors]
  -- framedParents gives the non-demoted group parent box
  have hboxMem : orig_x ∈ inp.boxes := List.mem_of_getElem? horigLookup
  obtain ⟨parentBox, hparentMem, hpid, hpgroup, hpnotfixed⟩ :=
    framedParents_parent hframed hboxMem hpxne
  have hnp : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == parentBox.id) = true) := by
    intro hc
    rw [hc] at hpnotfixed
    simp at hpnotfixed
  obtain ⟨p₀, hp₀⟩ := List.mem_iff_getElem?.mp hparentMem
  have hfbp : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box)[p₀]? = some parentBox := by
    simp only [List.getElem?_map, hp₀, Option.map_some, ite_eq_right hnp]
  have hp₀bound : p₀ < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hfbp).1
    rw [List.length_map] at hi
    omega
  obtain ⟨topP, bottomP, htopPlookup, hbotmem, htopPborder, hbotborder, htopdecl,
      hbotdecl, htopPpath, hbotpath, hbotw, hboth⟩ :=
    measuredGraph_paired_markers hgraph hp₀bound hfbp hpgroup
  clear bottomP hbotmem hbotborder htopdecl hbotdecl hbotpath hbotw hboth
  -- path transfers through the fixed-size demotion
  have hpathOrig : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) orig_x =
      Compound.path inp.boxes orig_x := by
    have h := Compound.path_map inp.boxes (fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) demote_id demote_parent hboxMem
    rw [ite_eq_right hnf] at h
    exact h
  have hpathParent : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) parentBox =
      Compound.path inp.boxes parentBox := by
    have h := Compound.path_map inp.boxes (fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) demote_id demote_parent hparentMem
    rw [ite_eq_right hnp] at h
    exact h
  have hpathStep : Compound.path inp.boxes orig_x =
      Compound.path inp.boxes parentBox ++ [p₀] :=
    Compound.path_of_parent (inputModel inp o) hwf hp₀ horigLookup (by rw [hpid]) hpxne
  have hdropFinal : topP.clusterPath = x.1.clusterPath.dropLast := by
    rw [htopPpath, hpathParent, ← hpathStep, ← hpathOrig, ← hdrop]
  -- the parent top sits in the same component through the child constraint edge
  have htopPzip : (topP, p₀) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopPlookup
  have htopZip : (x.1, oIdx) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsource
  obtain ⟨xb, hxbfind⟩ := groupTopFind?_some hgraph hlines htopZip hxGroup
  obtain ⟨pb, hpbfind⟩ := groupTopFind?_some hgraph hlines htopPzip htopPborder
  obtain ⟨heP, _⟩ := compound_child_constraint_edges htopPzip htopPborder hpbfind
    htopZip hxGroup hdropFinal.symm hxbfind
  obtain ⟨c, hcMem, hcP, hcO⟩ :=
    components_edge_endpoints hbd (List.mem_append_right _ heP)
  have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcO hoIn
  rw [hcEq] at hcP
  have htopPin : topP ∈ (componentCandidate graph comp candidate).nodes := by
    rw [componentCandidate_nodes]
    exact List.mem_map.mpr ⟨p₀, hcP, by
      rw [List.getD_eq_getElem?_getD, htopPlookup]
      rfl⟩
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp htopPin
  have hp : ((fun entry : Node × Nat =>
      entry.1.border == -2 && entry.1.clusterPath == x.1.clusterPath.dropLast)
      (topP, i₀)) = true := by
    simp [htopPborder, hdropFinal]
  exact findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hi₀) hp

end Elegant.Layered.PipelineImpl
