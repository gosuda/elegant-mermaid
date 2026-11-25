import Elegant.Layered.DummyRowClearProof
import Elegant.Layered.BottomNestedRankProof
import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.BottomClearanceExistence
set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! Proof of the dummy-row marker residual `DummyNestedMarkerBelow`.

A marker (top `-2` or bottom `2`) whose cluster path contains a bottom
proxy's owner ranks strictly below that proxy, unless it is the proxy
itself.  Route: same-group top below its own bottom
(`componentRun_group_top_lt_bottom`); nested marker below its own bottom,
which sits strictly below the outer bottom (transitive child-bottom
intervals along the cluster path, seeded by
`candidate_parent_top_exists`); distinct bottom with the same declaration
is impossible (`componentCandidate_bottom_find_eq`).  The bottom-vs-bottom
strict step reruns the `bnr_nested_bottom_rank` induction with a strict
conclusion, since `bottomNestedBottomRankLe_wf` only gives `≤`. -/

private theorem dn_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

private theorem dn_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

private theorem dn_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := dn_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact dn_take_is_prefix q p.length

private theorem dn_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := dn_prefix_take_eq h1
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

private theorem dn_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      dn_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (dn_prefix_antisymm hp h2) hne

private theorem dn_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
      cases as with
      | nil => exact ⟨[a], rfl⟩
      | cons b bs =>
          obtain ⟨r, hr⟩ := ih
          exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

private theorem dn_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

private theorem dn_group_box {P : Params} {inp : Input} {o : Options}
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

private theorem dn_bottom_box {P : Params} {inp : Input} {o : Options}
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

private theorem dn_scope_prefix {inp : Input} {o : Options}
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

private theorem dn_lines_length {m : Measure.Metric} {target : Int}
    {inp : Input} {lines : List (List Measure.Line)}
    (h : boxLines m target inp = .ok lines) : lines.length = inp.boxes.length := by
  unfold boxLines at h
  have hlen := (mapM_getElem? _ _ _ h).1
  have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
  omega

/-- Strict form of the nested-bottom induction: the bottom of a strictly
nested group top ranks strictly below the outer bottom.  The base case of
equal paths forces equal declarations (via path lasts), contradicting the
distinctness premise; the inductive step descends through the direct parent
(`candidate_parent_top_exists`) and chains the induction hypothesis with
the direct child-bottom edge (`ranked_compound_child_interval`). -/
private theorem strict_top_nested_bottom
    {P : Params} {inp : Input} {o : Options}
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
      nb.decl ≠ na.decl →
      rk rr.ranks bb.2 + 1 ≤ rk rr.ranks ba.2 := by
  have hparEx := candidate_parent_top_exists hgraph hlines hwf hfp hcomp candidate
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ba bb ha hbA hb hbB hpre hdelta hba hbb hne
    by_cases heq : na.clusterPath = nb.clusterPath
    · exfalso
      have hlastA : na.clusterPath.getLast? = some na.decl := by
        obtain ⟨boxA, _, hpathA⟩ := dn_group_box hgraph ha hbA
        exact dn_path_last hpathA
      have hlastB : nb.clusterPath.getLast? = some nb.decl := by
        obtain ⟨boxB, _, hpathB⟩ := dn_group_box hgraph hb hbB
        exact dn_path_last hpathB
      have hcon := congrArg List.getLast? heq
      rw [hlastA, hlastB] at hcon
      exact hne (Option.some.inj hcon).symm
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        dn_prefix_length_lt hpre heq
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
        dn_prefix_of_common_prefix hpre (huPath ▸ dn_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      obtain ⟨ubot, hubot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
      have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
      have hChildMem : (nb, b) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hb
      have hParMem : (u.1, u.2) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr huLookup
      by_cases hudecl : u.1.decl = na.decl
      · have hubotEq : ubot = ba := by
          rw [hudecl] at hubot
          exact Option.some.inj (hubot.symm.trans hba)
        have hinterv := ranked_compound_child_interval hrr hParMem huBorder hubot
          hChildMem hbB hpathUB hbb
        have hub2 : ubot.2 = ba.2 := congrArg Prod.snd hubotEq
        rw [hub2] at hinterv
        exact hinterv.2
      · have hIH := ih _ hdeltaU a u.2 na u.1 ba ubot ha hbA huLookup huBorder
          hpreU rfl hba hubot hudecl
        have hinterv := ranked_compound_child_interval hrr hParMem huBorder hubot
          hChildMem hbB hpathUB hbb
        omega

/-- The marker residual holds for every executed layout whose input model is
well-formed with framed parents: the two extra premises are exactly the
ones the `dummyRowClear` seam field already carries. -/
theorem dummyNestedMarkerBelow_wf {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) :
    DummyNestedMarkerBelow execution.params execution.graph := by
  intro comp hcomp candidate run labels orderOptions hrun t b owner htborder hlast hb hcontains
  have hgraph : measuredGraph execution.params inp o execution.lines =
      .ok execution.graph := execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length :=
    dn_lines_length execution.lines_eq
  obtain ⟨rr, labeled, hrr, hcoord, hkeys, hranks, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  cases hvt : run.coordinateProper.nodes[t]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hvt, Option.getD_none] at htborder
      have hd0 : (default : ProperNode).node.border = 0 := rfl
      omega
  | some ndT =>
  cases hvb : run.coordinateProper.nodes[b]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hvb, Option.getD_none] at hcontains
      have hnil : (default : ProperNode).node.clusterPath = [] := rfl
      rw [hnil] at hcontains
      simp at hcontains
  | some ndB =>
  have htD : run.coordinateProper.nodes.getD t default = ndT := by
    simp [List.getD_eq_getElem?_getD, hvt]
  have hbD : run.coordinateProper.nodes.getD b default = ndB := by
    simp [List.getD_eq_getElem?_getD, hvb]
  rw [htD] at htborder hlast
  rw [hbD] at hb hcontains
  rw [← hcoord] at hvt hvb
  rcases coordinateGraph_lookup execution.params labeled hvt with
    ⟨mt, hmt, _, hbT, hpT, _⟩ | ⟨_, hbPM⟩ | ⟨_, _, _, _, _, hbT3, _⟩
  · rcases coordinateGraph_lookup execution.params labeled hvb with
      ⟨mB, hmB, _, hbB, hpB, _⟩ | ⟨_, hbPMB⟩ | ⟨_, _, _, _, _, hbB3, _⟩
    · rcases hkeys t mt hmt with ⟨nT, hnT, hmdT, hnbT, hnpT⟩ | ⟨_, hb0, _⟩
      · rcases hkeys b mB hmB with ⟨nB, hnB, hmdB, hnBb, hnpB⟩ | ⟨_, hb0B, _⟩
        · have hmtB : mt.node.border = 2 := hbT.symm.trans htborder
          have hnTb : nT.border = 2 := hnbT.symm.trans hmtB
          have hpathT : ndT.node.clusterPath = nT.clusterPath :=
            (hpT hmdT).trans hnpT
          have hpathB : ndB.node.clusterPath = nB.clusterPath :=
            (hpB hmdB).trans hnpB
          have hnBbEq : nB.border = ndB.node.border := hnBb.symm.trans hbB.symm
          have hmemB : owner ∈ nB.clusterPath := by
            rw [← hpathB]
            exact hcontains
          have hlastDecl : nT.clusterPath.getLast? = some nT.decl := by
            obtain ⟨_, hoT, hsourceT⟩ :=
              componentCandidate_nonplain_source hnT (by rw [hnTb]; decide)
            obtain ⟨boxT, _, _, hpathBoxT, _, _⟩ :=
              measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsourceT) hnTb
            rw [hpathBoxT, List.getLast?_append]
            simp
          have howner : owner = nT.decl := by
            have h := congrArg List.getLast? hpathT
            rw [hlast, hlastDecl] at h
            exact Option.some.inj h
          have hcontainsN : nB.clusterPath.contains nT.decl = true := by
            rw [← howner]
            exact List.contains_iff_mem.mpr hmemB
          have htBound : t < (componentCandidate execution.graph comp candidate).nodes.length :=
            (List.getElem?_eq_some_iff.mp hnT).1
          have hbBound : b < (componentCandidate execution.graph comp candidate).nodes.length :=
            (List.getElem?_eq_some_iff.mp hnB).1
          have hfindT0 := componentCandidate_bottom_find_eq hgraph hcomp hnT hnTb
          obtain ⟨⟨ot, oi⟩, hTfind⟩ :=
            componentRun_cg_top_of_bottom hgraph hlines hcomp hnT hnTb
          have hTpred := List.find?_some hTfind
          simp only [Bool.and_eq_true, beq_iff_eq] at hTpred
          obtain ⟨htBorder, hTpEq⟩ := hTpred
          have hTmem : (ot, oi) ∈
              (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
            List.mem_of_find?_eq_some hTfind
          have hTlook : (componentCandidate execution.graph comp candidate).nodes[oi]? =
              some ot := List.mem_zipIdx_iff_getElem?.mp hTmem
          have hotDecl : ot.decl = nT.decl := by
            obtain ⟨boxO, _, hpathO⟩ := dn_group_box hgraph hTlook htBorder
            obtain ⟨_, _, hpathN⟩ := dn_bottom_box hgraph hnT hnTb
            have l1 : ot.clusterPath.getLast? = some ot.decl := dn_path_last hpathO
            have l2 : nT.clusterPath.getLast? = some nT.decl := dn_path_last hpathN
            have h := congrArg List.getLast? hTpEq
            rw [l1, l2] at h
            exact Option.some.inj h
          have hnBbDisj : nB.border = -2 ∨ nB.border = 2 := by
            rw [hnBbEq]
            exact hb
          rcases hnBbDisj with hnTop | hnBot
          · obtain ⟨nBbot, hnBbot⟩ :=
              componentRun_cg_bottom_find hgraph hlines hcomp hnB hnTop
            have hBpred := List.find?_some hnBbot
            simp only [Bool.and_eq_true, beq_iff_eq] at hBpred
            obtain ⟨hbbBord, hbbDecl⟩ := hBpred
            have hBbotMem : nBbot ∈
                (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
              List.mem_of_find?_eq_some hnBbot
            have hBbotLook : (componentCandidate execution.graph comp candidate).nodes[nBbot.2]? =
                some nBbot.1 := List.mem_zipIdx_iff_getElem?.mp hBbotMem
            obtain ⟨rr2, _, hrr2, _, _, _, _, H⟩ :=
              componentRun_group_top_lt_bottom hgraph hcomp hrun
            have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
            subst hrrEq
            have hle : rk rr.ranks b + 1 ≤ rk rr.ranks nBbot.2 :=
              H b nB nBbot hnB hnTop hnBbot
            have eB : rk run.coordinateProper.rank b = rk rr.ranks b := by
              have h1 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hbBound
              rw [hcoord] at h1
              exact h1
            have eT : rk run.coordinateProper.rank t = rk rr.ranks t := by
              have h1 := prepared_coordinate_original_rk (P := execution.params) hrr hranks htBound
              rw [hcoord] at h1
              exact h1
            by_cases hdeclEq : nB.decl = nT.decl
            · have hfindT : (componentCandidate execution.graph comp candidate).nodes.zipIdx.find?
                  (fun entry => entry.1.border == 2 && entry.1.decl == nB.decl) =
                  some (nT, t) := by
                rw [hdeclEq]
                exact hfindT0
              have hEq : nBbot = (nT, t) :=
                Option.some.inj (hnBbot.symm.trans hfindT)
              have hbit : nBbot.2 = t := congrArg Prod.snd hEq
              rw [hbit] at hle
              exact Or.inl (by omega)
            · have hbbPath : nBbot.1.clusterPath = nB.clusterPath := by
                obtain ⟨box1, hbox1, hpath1⟩ := dn_bottom_box hgraph hBbotLook hbbBord
                obtain ⟨box2, hbox2, hpath2⟩ := dn_group_box hgraph hnB hnTop
                rw [hbbDecl] at hbox1
                have hbeq : box1 = box2 := Option.some.inj (hbox1.symm.trans hbox2)
                rw [hpath1, hpath2, hbeq, hbbDecl]
              have hneInner : nBbot.1.decl ≠ ot.decl := by
                rw [hbbDecl, hotDecl]
                exact hdeclEq
              have hcontInner : nBbot.1.clusterPath.contains ot.decl = true := by
                rw [hbbPath, hotDecl]
                exact hcontainsN
              have hNBound : nBbot.2 <
                  (componentCandidate execution.graph comp candidate).nodes.length :=
                (List.getElem?_eq_some_iff.mp hBbotLook).1
              have eN : rk run.coordinateProper.rank nBbot.2 = rk rr.ranks nBbot.2 := by
                have h1 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hNBound
                rw [hcoord] at h1
                exact h1
              have hNest := bottomNestedBottomRankLe_wf hgraph hlines hwf hfp hcomp hrun
                hnT hTlook hnTb htBorder hotDecl.symm hBbotLook hbbBord hneInner hcontInner
              exact Or.inl (by omega)
          · by_cases heqB : b = t
            · exact Or.inr heqB
            · by_cases hdeclEq : nB.decl = nT.decl
              · have hfindB := componentCandidate_bottom_find_eq hgraph hcomp hnB hnBot
                have hfindTN : (componentCandidate execution.graph comp candidate).nodes.zipIdx.find?
                    (fun entry => entry.1.border == 2 && entry.1.decl == nB.decl) =
                    some (nT, t) := by
                  rw [hdeclEq]
                  exact hfindT0
                have hEq := Option.some.inj (hfindB.symm.trans hfindTN)
                have hbt : b = t := congrArg Prod.snd hEq
                exact (heqB hbt).elim
              · obtain ⟨⟨nt, ni⟩, hntFind⟩ :=
                  componentRun_cg_top_of_bottom hgraph hlines hcomp hnB hnBot
                have hntPred := List.find?_some hntFind
                simp only [Bool.and_eq_true, beq_iff_eq] at hntPred
                obtain ⟨hntBorder, hEqN⟩ := hntPred
                have hntMem : (nt, ni) ∈
                    (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
                  List.mem_of_find?_eq_some hntFind
                have hntLook : (componentCandidate execution.graph comp candidate).nodes[ni]? =
                    some nt := List.mem_zipIdx_iff_getElem?.mp hntMem
                have hntDecl : nt.decl = nB.decl := by
                  obtain ⟨boxI, _, hpathI⟩ := dn_group_box hgraph hntLook hntBorder
                  obtain ⟨_, _, hpathM⟩ := dn_bottom_box hgraph hnB hnBot
                  have l1 : nt.clusterPath.getLast? = some nt.decl := dn_path_last hpathI
                  have l2 : nB.clusterPath.getLast? = some nB.decl := dn_path_last hpathM
                  have h := congrArg List.getLast? hEqN
                  rw [l1, l2] at h
                  exact Option.some.inj h
                obtain ⟨boxO2, hboxO, hpathO⟩ := dn_group_box hgraph hTlook htBorder
                obtain ⟨boxI2, hboxI, hpathI⟩ := dn_group_box hgraph hntLook hntBorder
                have hcontNt : nt.clusterPath.contains ot.decl = true := by
                  rw [hotDecl, hEqN]
                  exact hcontainsN
                have hpreScope : ot.clusterPath <+: nt.clusterPath :=
                  dn_scope_prefix hwf hboxO hpathO hboxI hpathI hcontNt
                have hba : (componentCandidate execution.graph comp candidate).nodes.zipIdx.find?
                    (fun entry => entry.1.border == 2 && entry.1.decl == ot.decl) =
                    some (nT, t) := by
                  rw [hotDecl]
                  exact hfindT0
                have hfindB0 := componentCandidate_bottom_find_eq hgraph hcomp hnB hnBot
                have hbb : (componentCandidate execution.graph comp candidate).nodes.zipIdx.find?
                    (fun entry => entry.1.border == 2 && entry.1.decl == nt.decl) =
                    some (nB, b) := by
                  rw [hntDecl]
                  exact hfindB0
                have hneDecl : nt.decl ≠ ot.decl := by
                  rw [hntDecl, hotDecl]
                  exact hdeclEq
                have hstrict := strict_top_nested_bottom hgraph hlines hwf hfp hcomp
                  candidate hrr _ oi ni ot nt (nT, t) (nB, b) hTlook htBorder hntLook
                  hntBorder hpreScope rfl hba hbb hneDecl
                have hle : rk rr.ranks b + 1 ≤ rk rr.ranks t := hstrict
                have eB : rk run.coordinateProper.rank b = rk rr.ranks b := by
                  have h1 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hbBound
                  rw [hcoord] at h1
                  exact h1
                have eT : rk run.coordinateProper.rank t = rk rr.ranks t := by
                  have h1 := prepared_coordinate_original_rk (P := execution.params) hrr hranks htBound
                  rw [hcoord] at h1
                  exact h1
                exact Or.inl (by omega)
        · omega
      · omega
    · rcases hbPMB with _ | _ <;> omega
    · omega
  · rcases hbPM with _ | _ <;> omega
  · omega

/-- The dummy-row clearance seam holds for every executed well-formed layout
with framed parents, without the marker residual. -/
theorem dummyInsideProxyRowClear_executed' {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) :
    dummyInsideProxyRowClear execution.params execution.graph :=
  dummyInsideProxyRowClear_of_execution execution
    (dummyNestedRank execution (dummyNestedMarkerBelow_wf execution hwf hfp))

end Elegant.Layered.PipelineImpl
