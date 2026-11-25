import Elegant.Layered.SideMarkerAnchorCoverProof
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.BracketInsideRankFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem getElem_unique_id' {α : Type} {f : α → String} {l : List α}
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

/-- Every member of a `Compound.ancestors` walk is a group box (copied from
`ExclusiveKeyOutsideCgPathsProof`, whose copy is file-private). -/
private theorem path_member_group' {inp : Input} {o : Options}
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
            obtain ⟨hpbIdRoleB, _⟩ := Bool.and_eq_true_iff.mp hpb
            obtain ⟨hpbIdB, hpbRoleB⟩ := Bool.and_eq_true_iff.mp hpbIdRoleB
            have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
            have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
            have heq : b = pb :=
              getElem_unique_id' hids (List.mem_of_getElem? hb) hpbmem
                (he.trans hpbId.symm)
            subst heq
            exact ⟨b, hb, hpbRole⟩

/-- Every ancestor is a non-fixed group box. -/
private theorem path_member_group_nf' {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes)
    {i : Nat} (hin : i ∈ Compound.ancestors inp.boxes fuel c.parent) :
    ∃ b, inp.boxes[i]? = some b ∧ b.role = .group ∧
      inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == b.id) = false := by
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
            obtain ⟨hpbIdRoleB, hpbNf⟩ := Bool.and_eq_true_iff.mp hpb
            obtain ⟨hpbIdB, hpbRoleB⟩ := Bool.and_eq_true_iff.mp hpbIdRoleB
            have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
            have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
            have heq : b = pb :=
              getElem_unique_id' hids (List.mem_of_getElem? hb) hpbmem
                (he.trans hpbId.symm)
            subst heq
            have hnf : inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == b.id) = false := by
              simpa using hpbNf
            exact ⟨b, hb, hpbRole, hnf⟩
/-- Top-walk: any candidate `-2` node whose path carries `decl` yields the
candidate `-2` node of `decl`, by walking up parent tops. -/
private theorem topWalk
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) :
    ∀ (len : Nat) (idx : Nat) (n : Node) (decl : Nat),
      (componentCandidate graph comp candidate).nodes[idx]? = some n →
      n.border = -2 →
      n.clusterPath.contains decl = true →
      n.clusterPath.length = len →
      ∃ (u : Nat) (uNode : Node),
        (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧
        uNode.border = -2 ∧ uNode.decl = decl := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro idx n decl hn hb hcontains hlen
    by_cases hdeq : n.decl = decl
    · exact ⟨idx, n, hn, hb, hdeq⟩
    · have hpathNe : n.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph hn).2 hb
      obtain ⟨_, _, hsource⟩ :=
        componentCandidate_nonplain_source hn (by omega)
      obtain ⟨_, box, _, _, hpath⟩ :=
        measuredGraph_group_origin hgraph hsource hb
      have hmem : decl ∈ n.clusterPath :=
        List.contains_iff_mem.mp hcontains
      have hdropEq : n.clusterPath.dropLast =
          Compound.path (inp.boxes.map fun box =>
            if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
              ({ box with role := .node } : ModelBox) else box) box := by
        rw [hpath, List.dropLast_append_of_ne_nil (l := [n.decl]) (by simp)]
        simp
      have hmemPrefix : decl ∈ Compound.path (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
            ({ box with role := .node } : ModelBox) else box) box := by
        rw [hpath] at hmem
        rcases List.mem_append.mp hmem with h | h
        · exact h
        · have hsing : decl = n.decl := List.mem_singleton.mp h
          exact (hdeq hsing.symm).elim
      have hmemDrop : decl ∈ n.clusterPath.dropLast := by
        rw [hdropEq]; exact hmemPrefix
      have hpos : 0 < n.clusterPath.length :=
        List.length_pos_iff.mpr hpathNe
      have hdropLen : n.clusterPath.dropLast.length = len - 1 := by
        rw [List.length_dropLast, hlen]
      have hdropPrefix : n.clusterPath.dropLast <+: n.clusterPath :=
        List.dropLast_prefix _
      have hdropLt : n.clusterPath.dropLast.length < n.clusterPath.length := by
        have hdl : n.clusterPath.dropLast.length = n.clusterPath.length - 1 :=
          List.length_dropLast ..
        omega
      have hdropNe : n.clusterPath.dropLast ≠ [] :=
        List.ne_nil_of_mem hmemDrop
      have hparEx :=
        candidate_parent_top_exists hgraph hlines hwf hfp hcomp candidate
      have hxMem : (n, idx) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hn
      obtain ⟨parent, hparentFind⟩ :=
        hparEx (n, idx) hxMem hb n.clusterPath.dropLast hdropPrefix hdropLt hdropNe
      have hparentPred := List.find?_some hparentFind
      simp only [Bool.and_eq_true, beq_iff_eq] at hparentPred
      obtain ⟨huBorder, huPath⟩ := hparentPred
      have hparentMem : parent ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_of_find?_eq_some hparentFind
      have hparentLookup :
          (componentCandidate graph comp candidate).nodes[parent.2]? = some parent.1 :=
        List.mem_zipIdx_iff_getElem?.mp hparentMem
      have hparentContains : parent.1.clusterPath.contains decl = true := by
        have : decl ∈ parent.1.clusterPath := by rw [huPath]; exact hmemDrop
        exact List.contains_iff_mem.mpr this
      have hparentLen : parent.1.clusterPath.length = len - 1 := by
        rw [huPath, hdropLen]
      have hlt : len - 1 < len := by omega
      exact ih (len - 1) hlt parent.2 parent.1 decl hparentLookup huBorder
        hparentContains hparentLen

/-- Plain member to top: a candidate `border = 0` node whose path carries
`decl` puts `decl` in its component via the member constraint edge, yielding
the candidate `-2` node of `decl`. -/
private theorem plainToTop
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) :
    ∀ (idx : Nat) (n : Node) (decl : Nat),
      (componentCandidate graph comp candidate).nodes[idx]? = some n →
      n.border = 0 →
      n.clusterPath.contains decl = true →
      ∃ (u : Nat) (uNode : Node),
        (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧
        uNode.border = -2 ∧ uNode.decl = decl := by
  intro idx n decl hn hb hcontains
  have hpathNe : n.clusterPath ≠ [] := by
    intro hempty
    simp [hempty] at hcontains
  obtain ⟨oIdx, ho, hsource⟩ :=
    componentCandidate_nonempty_path_source hn hpathNe
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? ho
  obtain ⟨nodes0, edges0, titles0, hprep, hlen0, hmeta⟩ :=
    measuredGraph_prepared_source hgraph
  let boxesM := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
      ({ box with role := .node } : ModelBox) else box
  have hnodes : graph.nodes =
      (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)) ++ markExtras boxesM := by
    rw [hprep]
    rfl
  have hmappedLen : (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length =
      nodes0.length := by simp
  have hoLtMapped : oIdx <
      (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length := by
    by_cases hlt : oIdx <
        (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length
    · exact hlt
    · have hge : (nodes0.zipIdx.map
          (markOne boxesM P.clusterPad titles0)).length ≤ oIdx :=
        Nat.le_of_not_gt hlt
      have hextra : (markExtras boxesM)[oIdx -
          (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length]? = some n := by
        have heq : graph.nodes[oIdx]? = some n := hsource
        rw [hnodes, List.getElem?_append_right hge] at heq
        exact heq
      have hmem : n ∈ markExtras boxesM := List.mem_of_getElem? hextra
      have hb2 : n.border = 2 := markExtras_border _ hmem
      omega
  have hoLtNodes : oIdx < nodes0.length := by omega
  have hoLtBoxes : oIdx < boxesM.length := by
    have h1 : boxesM.length = inp.boxes.length := by simp [boxesM]
    have h2 : nodes0.length = lines.length := hlen0
    omega
  obtain ⟨boxM, hboxM⟩ : ∃ boxM, boxesM[oIdx]? = some boxM :=
    ⟨_, List.getElem?_eq_getElem hoLtBoxes⟩
  have hnodePrep : (Compound.prepare boxesM P.clusterPad titles0
      { nodes := nodes0, edges := edges0, slot := P.slot }).nodes[oIdx]? = some n := by
    rw [← hprep]; exact hsource
  obtain ⟨_, hpathN⟩ :=
    prepare_plain_path_origin boxesM P.clusterPad titles0 _ hmeta hnodePrep hb hboxM
  obtain ⟨origBox, horigBox, hchangeBox⟩ : ∃ origBox, inp.boxes[oIdx]? = some origBox ∧
      boxM = (if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == origBox.id) then
        ({ origBox with role := .node } : ModelBox) else origBox) := by
    rw [List.getElem?_map] at hboxM
    obtain ⟨origBox, horigBox, hchangeBox⟩ := Option.map_eq_some_iff.mp hboxM
    exact ⟨origBox, horigBox, hchangeBox.symm⟩
  obtain ⟨_, _, hpathMap0⟩ := fixedSizes_path_index inp horigBox
  have hpathInp : n.clusterPath = Compound.path inp.boxes origBox := by
    rw [hpathN, hchangeBox]
    exact hpathMap0
  have hmemInp : decl ∈ Compound.path inp.boxes origBox := by
    rw [← hpathInp]; exact List.contains_iff_mem.mp hcontains
  have hpathEq : Compound.path inp.boxes origBox =
      Compound.ancestors inp.boxes inp.boxes.length origBox.parent := rfl
  have hmemAnc : decl ∈ Compound.ancestors inp.boxes inp.boxes.length origBox.parent := by
    rw [← hpathEq]; exact hmemInp
  obtain ⟨declBox, hboxDecl, hroleDecl, hnfDecl⟩ :=
    path_member_group_nf' hwf hfp inp.boxes.length origBox (List.mem_of_getElem? horigBox) hmemAnc
  have hdeclLt : decl < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hboxDecl).1
    omega
  have hlenBoxesM : boxesM.length = inp.boxes.length := by simp [boxesM]
  have hdeclLtM : decl < boxesM.length := by omega
  have hboxDeclM : boxesM[decl]? = some declBox := by
    simp [boxesM, hboxDecl, hnfDecl]
  obtain ⟨top0, bottom0, htop0, hbotmem, htopBorder, hbotBorder, htopDecl, hbotDecl, _, _, _, _⟩ :=
    measuredGraph_paired_markers hgraph hdeclLt hboxDeclM hroleDecl
  have htopIdx : graph.nodes[decl]? = some top0 := htop0
  have htopZip : (top0, decl) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopIdx
  have hmemZip : (n, oIdx) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsource
  obtain ⟨bIdx, hbIdx⟩ := List.mem_iff_getElem?.mp hbotmem
  have hbotZip : (bottom0, bIdx) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hbIdx
  have hbotPred : (fun entry : Node × Nat => entry.1.border == 2 && entry.1.decl == top0.decl)
      (bottom0, bIdx) = true := by
    have e1 : bottom0.border = 2 := hbotBorder
    have e2 : bottom0.decl = top0.decl := by rw [hbotDecl, htopDecl]
    simp [e1, e2]
  obtain ⟨bottomG, hfindG⟩ : ∃ bottomG : Node × Nat,
      (graph.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == top0.decl) = some bottomG :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(bottom0, bIdx), hbotZip, hbotPred⟩)
  have hinside : n.clusterPath.contains top0.decl = true := by
    rw [htopDecl]; exact hcontains
  obtain ⟨he1, _⟩ := compound_member_constraint_edges htopZip htopBorder hfindG hmemZip hb hinside
  have hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact measuredGraph_edges_bounded hgraph hlines e he
    · exact constraints_bounded graph e he
  obtain ⟨c, hcMem, hcTail, hcHead⟩ :=
    components_edge_endpoints hbd (List.mem_append_right _ he1)
  have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcHead hoIn
  have hdeclInComp : decl ∈ comp := by rw [← hcEq]; exact hcTail
  have hmemCg : top0 ∈ (componentGraph graph comp).nodes := by
    apply List.mem_map.mpr ⟨decl, hdeclInComp, ?_⟩
    rw [List.getD_eq_getElem?_getD, htopIdx, Option.getD_some]
  obtain ⟨u, hu⟩ := List.mem_iff_getElem?.mp hmemCg
  have hcand : (componentCandidate graph comp candidate).nodes[u]? = some top0 := by
    rw [componentCandidate_nodes]
    exact hu
  exact ⟨u, top0, hcand, htopBorder, htopDecl⟩
/-- Bottom to top: a candidate `border = 2` node whose path carries `decl`
yields the candidate `-2` node of `decl`, via the paired top and the top-walk. -/
private theorem bottomToTop
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) :
    ∀ (idx : Nat) (n : Node) (decl : Nat),
      (componentCandidate graph comp candidate).nodes[idx]? = some n →
      n.border = 2 →
      n.clusterPath.contains decl = true →
      ∃ (u : Nat) (uNode : Node),
        (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧
        uNode.border = -2 ∧ uNode.decl = decl := by
  intro idx n decl hn hb hcontains
  obtain ⟨t, hfind⟩ := componentRun_cg_top_of_bottom hgraph hlines hcomp hn hb
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨htBorder, htPath⟩ := hpred
  have htMem : t ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mem_of_find?_eq_some hfind
  have htLookup : (componentCandidate graph comp candidate).nodes[t.2]? = some t.1 :=
    List.mem_zipIdx_iff_getElem?.mp htMem
  have htContains : t.1.clusterPath.contains decl = true := by
    rw [htPath]; exact hcontains
  exact topWalk hgraph hlines hwf hfp hcomp candidate t.1.clusterPath.length
    t.2 t.1 decl htLookup htBorder htContains rfl

/-- Any candidate node whose path carries `decl` yields the candidate `-2`
node of `decl`. -/
private theorem candidateTopExists
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) :
    ∀ (idx : Nat) (n : Node) (decl : Nat),
      (componentCandidate graph comp candidate).nodes[idx]? = some n →
      n.clusterPath.contains decl = true →
      ∃ (u : Nat) (uNode : Node),
        (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧
        uNode.border = -2 ∧ uNode.decl = decl := by
  intro idx n decl hn hcontains
  have hshape := (componentCandidate_marker_shape hgraph hn).1
  rcases hshape with hb0 | hb2 | hbB
  · exact plainToTop hgraph hlines hwf hfp hcomp candidate idx n decl hn hb0 hcontains
  · exact topWalk hgraph hlines hwf hfp hcomp candidate n.clusterPath.length
      idx n decl hn hb2 hcontains rfl
  · exact bottomToTop hgraph hlines hwf hfp hcomp candidate idx n decl hn hbB hcontains

theorem sideMarkerTopInCandidate : SideMarkerTopInCandidate := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
    orderOptions hrun decl low lowNd hlow hcontainLow
  have hqmem : (lowNd, low) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hlow
  by_cases hdum : lowNd.dummy = true
  · have howner : decl ∈ lowNd.node.clusterPath :=
      List.contains_iff_mem.mp hcontainLow
    have hlen : low < run.proper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hlow).1
    have hgetD : run.proper.nodes.getD low default = lowNd := by
      rw [List.getD_eq_getElem?_getD, hlow, Option.getD_some]
    have hdumG : (run.proper.nodes.getD low default).dummy = true := by
      rw [hgetD]; exact hdum
    have hownerG : decl ∈ (run.proper.nodes.getD low default).node.clusterPath := by
      rw [hgetD]; exact howner
    obtain ⟨index, edge, hedge, _, htailLt, _, _, _, nA, _, hnA, _, hcontA, _⟩ :=
      dummy_chain_bracket hrun hlen hdumG hownerG
    obtain ⟨u, uNode, hu, hbU, hdeclU⟩ :=
      candidateTopExists hgraph hlines hwf hfp hcomp candidate edge.tail nA decl hnA hcontA
    exact ⟨u, uNode, hu, hbU, hdeclU⟩
  · have hdumF : lowNd.dummy = false := by
      cases h : lowNd.dummy <;> simp_all
    obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := fbs_coordinate_record hrun hlow
    obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
      componentRun_prepared_titled_source hgraph hcomp hrun
    have hncL : (coordinateGraph P labeled).nodes[low]? = some nvc := by
      rw [hc]; exact hnc
    have hpathEq : nvc.node.clusterPath = lowNd.node.clusterPath := by
      by_cases hpx : nvc.node.border = -2 ∨ nvc.node.border = 2
      · obtain ⟨_, span, _, _, hproper, _, _, _⟩ :=
          componentRun_proxy_interval hrun hnc hpx
        have heq : lowNd =
            { nvc with node := { nvc.node with w := span.hi - span.lo } } :=
          Option.some.inj (hlow.symm.trans hproper)
        rw [heq]
      · obtain ⟨hrecFull, _⟩ := componentRun_nonproxy_record hrun hnc hpx
        have heq : lowNd = nvc := Option.some.inj (hlow.symm.trans hrecFull)
        rw [heq]
    have hdumEq : nvc.dummy = lowNd.dummy := by
      by_cases hpx : nvc.node.border = -2 ∨ nvc.node.border = 2
      · obtain ⟨_, span, _, _, hproper, _, _, _⟩ :=
          componentRun_proxy_interval hrun hnc hpx
        have heq : lowNd =
            { nvc with node := { nvc.node with w := span.hi - span.lo } } :=
          Option.some.inj (hlow.symm.trans hproper)
        rw [heq]
      · obtain ⟨hrecFull, _⟩ := componentRun_nonproxy_record hrun hnc hpx
        have heq : lowNd = nvc := Option.some.inj (hlow.symm.trans hrecFull)
        rw [heq]
    have hcontainNvc : nvc.node.clusterPath.contains decl = true := by
      rw [hpathEq]; exact hcontainLow
    rcases coordinateGraph_lookup P labeled hncL with
      ⟨m, hm, hmd, hbM, hpM, _⟩ | hside | ⟨iT, qt, hqt, hvT, hdT, hbT, hpT⟩
    · rcases hk low m hm with ⟨n, hn, hreal, hbN, hpN⟩ | ⟨hdT, _, _⟩
      · have hmdF : m.dummy = false := hreal
        have hpathM : nvc.node.clusterPath = m.node.clusterPath := hpM hmdF
        have hcontN : n.clusterPath.contains decl = true := by
          have h1 : m.node.clusterPath.contains decl = true := by
            rw [← hpathM]; exact hcontainNvc
          rw [← hpN]; exact h1
        obtain ⟨u, uNode, hu, hbU, hdeclU⟩ :=
          candidateTopExists hgraph hlines hwf hfp hcomp candidate low n decl hn hcontN
        exact ⟨u, uNode, hu, hbU, hdeclU⟩
      · have hnvcdum : nvc.dummy = true := by rw [hmd]; exact hdT
        have hlowdum : lowNd.dummy = true := by rw [← hdumEq]; exact hnvcdum
        exact (hdum hlowdum).elim
    · obtain ⟨top, htopMem, bottom, hfindB, hpathEqSide, _, _, _⟩ :=
        coordinateGraph_side_rank_bounds hready hncL hside.2
      have htopGet : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
          some top.1 :=
        List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
      have htopBorder : top.1.node.border = -2 := by
        have hcond := (List.mem_filter.mp htopMem).2
        simpa using hcond
      obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
        titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
      have htopCgBorder : topOrig.border = -2 := htopBorderEq.symm.trans htopBorder
      have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
        rw [htopRecord]; exact (titleF_keys _).2.2.1
      have hcontOrig : topOrig.clusterPath.contains decl = true := by
        have h1 : top.1.node.clusterPath.contains decl = true := by
          rw [← hpathEqSide]; exact hcontainNvc
        rw [← htopPath]; exact h1
      obtain ⟨u, uNode, hu, hbU, hdeclU⟩ :=
        topWalk hgraph hlines hwf hfp hcomp candidate topOrig.clusterPath.length
          top.2 topOrig decl htopCg htopCgBorder hcontOrig rfl
      exact ⟨u, uNode, hu, hbU, hdeclU⟩
    · have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
        (measuredGraph_shape hgraph) candidate
      have haligned : labeled.nodes.length = labeled.rank.length :=
        source_alignment_of_titled hready.2.2.2.1
      obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath, _⟩ :=
        coordinateGraph_title_rank_source hk hshape haligned hncL hbT
      have hcontOrig : original.node.clusterPath.contains decl = true := by
        rw [← htitlePath]; exact hcontainNvc
      rcases hk originalIndex original horiginal with
        ⟨n, hn, _, hborderN, hpathN⟩ | ⟨hdT2, _, _⟩
      · have hnBorder : n.border = -2 := hborderN.symm.trans hOrigBorder
        have hcontN : n.clusterPath.contains decl = true := by
          rw [← hpathN]; exact hcontOrig
        obtain ⟨u, uNode, hu, hbU, hdeclU⟩ :=
          topWalk hgraph hlines hwf hfp hcomp candidate n.clusterPath.length
            originalIndex n decl hn hnBorder hcontN rfl
        exact ⟨u, uNode, hu, hbU, hdeclU⟩
      · rw [hdT2] at hOrigReal
        simp at hOrigReal

/-- The executed side-marker anchor cover, with all residuals discharged. -/
theorem sideMarkerAnchorCover' : SideMarkerAnchorCover :=
  sideMarkerAnchorCover foreignBottomInCandidate sideMarkerTopInCandidate
    topMemberRankLe bottomMemberRankCover

/-- The bracket marker pair cover, with the anchor cover closed. -/
theorem bracketMarkersAtRank' : BracketMarkersAtRank :=
  bracketMarkersAtRank sideMarkerAnchorCover'

end Elegant.Layered.PipelineImpl
