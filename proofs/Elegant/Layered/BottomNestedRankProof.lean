import Elegant.Layered.GroupBottomBoundaryProof
set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem bnr_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

private theorem bnr_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

private theorem bnr_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := bnr_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact bnr_take_is_prefix q p.length

private theorem bnr_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := bnr_prefix_take_eq h1
  have hle1 : p.length ≤ q.length := by
    obtain ⟨r, rfl⟩ := h1
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hle2 : q.length ≤ p.length := by
    obtain ⟨r, rfl⟩ := h2
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hlen : p.length = q.length := by omega
  have e2 : q.take q.length = q := by simp
  rw [← hlen] at e2
  exact e.symm.trans e2

private theorem bnr_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      bnr_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (bnr_prefix_antisymm hp h2) hne

private theorem bnr_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

private theorem bnr_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

private theorem bnr_cg_group_box {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨_, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  rw [← hdecl] at hbox
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath

private theorem bnr_cg_bottom_box {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨_, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨boxD, hboxD, hroleD, hpathD, _, _⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hborder
  rw [List.getElem?_map] at hboxD
  obtain ⟨orig, horig, hchange⟩ := Option.map_eq_some_iff.mp hboxD
  have hnotfixed : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == orig.id) = true) := by
    intro hfixed
    have heq : ({ orig with role := .node } : ModelBox) = boxD := by
      simpa [hfixed] using hchange
    rw [← heq] at hroleD
    simp at hroleD
  have hboxEq : boxD = orig := by
    have hif : (if inp.fixedSizes.any (fun fixed : String × Size =>
        fixed.1 == orig.id) then ({ orig with role := .node } : ModelBox)
        else orig) = orig := ite_eq_right hnotfixed
    simpa [hif] using hchange.symm
  obtain ⟨_, _, hpathMap0⟩ := fixedSizes_path_index inp horig
  have hpathMap : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        ({ box with role := .node } : ModelBox) else box) orig =
      Compound.path inp.boxes orig := by
    simpa [hnotfixed] using hpathMap0
  refine ⟨orig, horig, ?_⟩
  rw [hboxEq] at hpathD
  rw [hpathD, hpathMap]

private theorem bnr_cg_scope_prefix {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o))
    {tbox mbox : ModelBox} {td md : Nat} {tpath mpath : List Nat}
    (htbox : inp.boxes[td]? = some tbox)
    (htpath : tpath = Compound.path inp.boxes tbox ++ [td])
    (hmbox : inp.boxes[md]? = some mbox)
    (hmpath : mpath = Compound.path inp.boxes mbox ++ [md])
    (hin : mpath.contains td = true) :
    tpath <+: mpath := by
  have hmem : td ∈ mpath := List.contains_iff_mem.mp hin
  rw [hmpath, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · have hpre := Compound.path_ancestor_prefix (inputModel inp o) hwf htbox hmbox hleft
    rw [htpath]
    exact hpre.trans ⟨[md], hmpath.symm⟩
  · have htd : td = md := by
      have h := hright
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact h
    subst htd
    have hbox : mbox = tbox := Option.some.inj (hmbox.symm.trans htbox)
    subst hbox
    rw [htpath, hmpath]
    exact List.prefix_refl _

private theorem bnr_cg_top_unique {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbA : na.border = -2) (hbB : nb.border = -2)
    (hpath : na.clusterPath = nb.clusterPath) : a = b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := bnr_cg_group_box hgraph ha hbA
    exact bnr_cg_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := bnr_cg_group_box hgraph hb hbB
    exact bnr_cg_path_last hpathB
  have hdecl : na.decl = nb.decl := by
    have h := congrArg List.getLast? hpath
    rw [hlastA, hlastB] at h
    exact Option.some.inj h
  obtain ⟨aSrc, haSrc, hsa⟩ := componentCandidate_nonplain_source ha (by omega)
  obtain ⟨bSrc, hbSrc, hsb⟩ := componentCandidate_nonplain_source hb (by omega)
  obtain ⟨hdeclA, _, _, _, _⟩ := measuredGraph_group_origin hgraph hsa hbA
  obtain ⟨hdeclB, _, _, _, _⟩ := measuredGraph_group_origin hgraph hsb hbB
  have hsrc : aSrc = bSrc := by omega
  exact nodup_map_inj_aux (fun x => x)
    (by simpa using components_nodup graph comp hcomp) haSrc hbSrc hsrc

private theorem bnr_nested_bottom_rank {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr) :
    ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node, ∀ ba bb : Node × Nat,
      (componentCandidate graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.clusterPath <+: nb.clusterPath →
      nb.clusterPath.length - na.clusterPath.length = delta →
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == na.decl) = some ba →
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == nb.decl) = some bb →
      rk rr.ranks bb.2 ≤ rk rr.ranks ba.2 := by
  have hparEx := candidate_parent_top_exists hgraph hlines hwf hfp hcomp candidate
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ba bb ha hbA hb hbB hpre hdelta hba hbb
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := bnr_cg_top_unique hgraph hcomp ha hb hbA hbB heq
      subst hab
      have hdecl : na.decl = nb.decl := by
        have hlastA : na.clusterPath.getLast? = some na.decl := by
          obtain ⟨box, hbox, hpathA⟩ := bnr_cg_group_box hgraph ha hbA
          exact bnr_cg_path_last hpathA
        have hlastB : nb.clusterPath.getLast? = some nb.decl := by
          obtain ⟨box, hbox, hpathB⟩ := bnr_cg_group_box hgraph hb hbB
          exact bnr_cg_path_last hpathB
        have h := congrArg List.getLast? heq
        rw [hlastA, hlastB] at h
        exact Option.some.inj h
      rw [hdecl] at hba
      have hbb_eq : bb = ba := Option.some.inj (hbb.symm.trans hba)
      rw [hbb_eq]
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        bnr_prefix_length_lt hpre heq
      have hbne : nb.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph hb).2 hbB
      have hna_ne : na.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph ha).2 hbA
      obtain ⟨u, hu⟩ := hparEx (nb, b)
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB na.clusterPath hpre hlt hna_ne
      have huPred := List.find?_some hu
      simp only [Bool.and_eq_true, beq_iff_eq] at huPred
      obtain ⟨huBorder, huPath⟩ := huPred
      have huMem : u ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_of_find?_eq_some hu
      have huLookup : (componentCandidate graph comp candidate).nodes[u.2]? = some u.1 :=
        List.mem_zipIdx_iff_getElem?.mp huMem
      have hdropLen : u.1.clusterPath.length = nb.clusterPath.length - 1 := by
        rw [huPath]
        exact List.length_dropLast ..
      have hnbpos : 0 < nb.clusterPath.length :=
        Nat.pos_of_ne_zero (fun h => hbne (List.length_eq_zero_iff.mp h))
      have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
      have hpreU : na.clusterPath <+: u.1.clusterPath :=
        bnr_prefix_of_common_prefix hpre (huPath ▸ bnr_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      obtain ⟨ubot, hubot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
      have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
      have hIH := ih _ hdeltaU a u.2 na u.1 ba ubot ha hbA huLookup huBorder hpreU rfl hba hubot
      have hinterv := ranked_compound_child_interval (parent := (u.1, u.2))
        (child := (nb, b)) hrr
        (List.mem_zipIdx_iff_getElem?.mpr huLookup) huBorder hubot
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpathUB hbb
      omega

theorem bottomNestedBottomRankLe_wf
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2) (hdecl : ndV.decl = ndT.decl)
    {j : Nat} {nb : Node}
    (hjGet : (componentCandidate graph comp candidate).nodes[j]? = some nb)
    (hbordJ : nb.border = 2) (hne : nb.decl ≠ ndT.decl)
    (hcontains : nb.clusterPath.contains ndT.decl = true) :
    rk run.coordinateProper.rank j ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, _, hranks, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  have _hne_use : nb.decl ≠ ndT.decl := hne
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
    have hfindV := componentCandidate_bottom_find_eq hgraph hcomp hvGet hbordV
    rw [← hdecl]
    exact hfindV
  obtain ⟨tn, htnFind⟩ := componentRun_cg_top_of_bottom hgraph hlines hcomp hjGet hbordJ
  have htnPred := List.find?_some htnFind
  simp only [Bool.and_eq_true, beq_iff_eq] at htnPred
  obtain ⟨htnBorder, htnPathEq⟩ := htnPred
  have htnMem : tn ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mem_of_find?_eq_some htnFind
  have htnLookup : (componentCandidate graph comp candidate).nodes[tn.2]? = some tn.1 :=
    List.mem_zipIdx_iff_getElem?.mp htnMem
  have hdeclTn : tn.1.decl = nb.decl := by
    have hlastTn : tn.1.clusterPath.getLast? = some tn.1.decl := by
      obtain ⟨box, hbox, hpathTn⟩ := bnr_cg_group_box hgraph htnLookup htnBorder
      exact bnr_cg_path_last hpathTn
    obtain ⟨boxM, hboxM, hpathM⟩ := bnr_cg_bottom_box hgraph hjGet hbordJ
    have hlastM : nb.clusterPath.getLast? = some nb.decl :=
      bnr_cg_path_last hpathM
    have h := congrArg List.getLast? htnPathEq
    rw [hlastTn, hlastM] at h
    exact Option.some.inj h
  obtain ⟨tnBot, htnBot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp htnLookup htnBorder
  have hfindNb : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == nb.decl) = some (nb, j) :=
    componentCandidate_bottom_find_eq hgraph hcomp hjGet hbordJ
  have htnBotEq : tnBot = (nb, j) := by
    rw [← hdeclTn] at hfindNb
    exact Option.some.inj (htnBot.symm.trans hfindNb)
  obtain ⟨boxT, hboxT, hpathT⟩ := bnr_cg_group_box hgraph htGet hbordT
  obtain ⟨boxM, hboxM, hpathM⟩ := bnr_cg_bottom_box hgraph hjGet hbordJ
  have hpreOuter : ndT.clusterPath <+: nb.clusterPath :=
    bnr_cg_scope_prefix hwf hboxT hpathT hboxM hpathM hcontains
  have hpre : ndT.clusterPath <+: tn.1.clusterPath := by
    rw [htnPathEq]
    exact hpreOuter
  have hrank := bnr_nested_bottom_rank hgraph hlines hwf hframed hcomp candidate hrr
    _ t tn.2 ndT tn.1 (ndV, v) tnBot htGet hbordT htnLookup htnBorder hpre rfl
    hbotFindOuter htnBot
  have hjEq : tnBot.2 = j := congrArg Prod.snd htnBotEq
  rw [hjEq] at hrank
  have hvEq : ((ndV, v) : Node × Nat).2 = v := rfl
  rw [hvEq] at hrank
  have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranks
      (List.getElem?_eq_some_iff.mp hvGet).1
    rw [hc] at h1
    exact h1
  have eJ : rk run.coordinateProper.rank j = rk rr.ranks j := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranks
      (List.getElem?_eq_some_iff.mp hjGet).1
    rw [hc] at h1
    exact h1
  omega

end Elegant.Layered.PipelineImpl
