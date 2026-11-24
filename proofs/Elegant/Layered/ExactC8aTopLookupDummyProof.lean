import Elegant.Layered.ExactC8aTopLookupProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.CoordGraph
import Elegant.Layered.GroupWidthFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-- File-unique prefix for all private helpers in this module. -/
private theorem c8aDM_exactRev {P : Params} {exactIds : List String} {inp : Input}
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

private theorem c8aDM_getElem_unique {α : Type} {f : α → String} {l : List α}
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

private theorem c8aDM_path_member_group_nf {inp : Input} {o : Options}
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
              c8aDM_getElem_unique hids (List.mem_of_getElem? hb) hpbmem
                (he.trans hpbId.symm)
            subst heq
            have hnf : inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == b.id) = false := by
              simpa using hpbNf
            exact ⟨b, hb, hpbRole, hnf⟩

private theorem c8aDM_topWalk {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel} (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) : ∀ (len : Nat) (idx : Nat) (n : Node) (decl : Nat),
    (componentCandidate graph comp candidate).nodes[idx]? = some n → n.border = -2 →
    n.clusterPath.contains decl = true → n.clusterPath.length = len →
    ∃ (u : Nat) (uNode : Node), (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧ uNode.border = -2 ∧ uNode.decl = decl := by
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
    intro idx n decl hn hb hcontains hlen
    by_cases hdeq : n.decl = decl
    · exact ⟨idx, n, hn, hb, hdeq⟩
    · have hpathNe : n.clusterPath ≠ [] := (X_componentCandidate_marker_shape h0 h hn).2 hb
      obtain ⟨box, _, hpath⟩ := X_cg_group_box h0 h hn hb
      have hmem : decl ∈ n.clusterPath := List.contains_iff_mem.mp hcontains
      rw [hpath] at hmem
      have hmemPre : decl ∈ Compound.path inp.boxes box := by
        rcases List.mem_append.mp hmem with h | h
        · exact h
        · have hsing : decl = n.decl := List.mem_singleton.mp h
          exact (hdeq hsing.symm).elim
      have hdropEq : n.clusterPath.dropLast = Compound.path inp.boxes box := by
        rw [hpath, List.dropLast_append_of_ne_nil (l := [n.decl]) (by simp)]
        simp
      have hmemDrop : decl ∈ n.clusterPath.dropLast := by rw [hdropEq]; exact hmemPre
      have hdropLen : n.clusterPath.dropLast.length = len - 1 := by
        rw [List.length_dropLast, hlen]
      have hdropPrefix : n.clusterPath.dropLast <+: n.clusterPath := List.dropLast_prefix _
      have hdropLt : n.clusterPath.dropLast.length < n.clusterPath.length := by
        have hdl : n.clusterPath.dropLast.length = n.clusterPath.length - 1 := List.length_dropLast ..
        have hpos : 0 < n.clusterPath.length := List.length_pos_iff.mpr hpathNe
        omega
      have hdropNe : n.clusterPath.dropLast ≠ [] := List.ne_nil_of_mem hmemDrop
      have hxMem : (n, idx) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hn
      obtain ⟨parent, hparentFind⟩ := X_candidate_parent_top_exists h0 h hlines hwf hfp hcomp candidate hxMem hb hdropPrefix hdropLt hdropNe
      have hparentPred := List.find?_some hparentFind
      simp only [Bool.and_eq_true, beq_iff_eq] at hparentPred
      obtain ⟨huBorder, huPath⟩ := hparentPred
      have hparentMem : parent ∈ (componentCandidate graph comp candidate).nodes.zipIdx := List.mem_of_find?_eq_some hparentFind
      have hparentLookup : (componentCandidate graph comp candidate).nodes[parent.2]? = some parent.1 := List.mem_zipIdx_iff_getElem?.mp hparentMem
      have hparentContains : parent.1.clusterPath.contains decl = true := by
        have : decl ∈ parent.1.clusterPath := by rw [huPath]; exact hmemDrop
        exact List.contains_iff_mem.mpr this
      have hparentLen : parent.1.clusterPath.length = len - 1 := by rw [huPath, hdropLen]
      have hlt : len - 1 < len := by have hpos : 0 < n.clusterPath.length := List.length_pos_iff.mpr hpathNe; rw [hlen] at hpos; omega
      exact ih (len - 1) hlt parent.2 parent.1 decl hparentLookup huBorder hparentContains hparentLen

private theorem c8aDM_plainToTop {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel} (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) (idx : Nat) (n : Node) (decl : Nat)
    (hn : (componentCandidate graph comp candidate).nodes[idx]? = some n)
    (hb : n.border = 0) (hcontains : n.clusterPath.contains decl = true) :
    ∃ (u : Nat) (uNode : Node), (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧ uNode.border = -2 ∧ uNode.decl = decl := by
  have hpathNe : n.clusterPath ≠ [] := by intro hempty; simp [hempty] at hcontains
  obtain ⟨oIdx, ho, hsource⟩ := componentCandidate_nonempty_path_source hn hpathNe
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? ho
  obtain ⟨n0, hsource0, hb0rev, hpath0rev, hdecl0rev⟩ := c8aDM_exactRev h hsource
  have hb0 : n0.border = 0 := by rw [← hb0rev]; exact hb
  have hcontains0 : n0.clusterPath.contains decl = true := by rw [← hpath0rev]; exact hcontains
  obtain ⟨nodes0, edges0, titles0, hprep, hlen0, hmeta⟩ := measuredGraph_prepared_source h0
  let boxesM := inp.boxes.map fun box => if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then ({ box with role := .node } : ModelBox) else box
  have hnodes0 : graph0.nodes = (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)) ++ markExtras boxesM := by rw [hprep]; rfl
  have hmappedLen : (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length = nodes0.length := by simp
  have hoLtMapped : oIdx < (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length := by
    by_cases hlt : oIdx < (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length
    · exact hlt
    · have hge : (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length ≤ oIdx := Nat.le_of_not_gt hlt
      have hextra : (markExtras boxesM)[oIdx - (nodes0.zipIdx.map (markOne boxesM P.clusterPad titles0)).length]? = some n0 := by
        have heq : graph0.nodes[oIdx]? = some n0 := hsource0
        rw [hnodes0, List.getElem?_append_right hge] at heq; exact heq
      have hmem : n0 ∈ markExtras boxesM := List.mem_of_getElem? hextra
      have hb2 : n0.border = 2 := markExtras_border _ hmem
      omega
  have hoLtNodes : oIdx < nodes0.length := by omega
  have hlenBM : boxesM.length = inp.boxes.length := by simp [boxesM]
  have hlenNL : nodes0.length = lines.length := hlen0
  have hoLtBoxes : oIdx < boxesM.length := by omega
  obtain ⟨boxM, hboxM⟩ : ∃ boxM, boxesM[oIdx]? = some boxM := ⟨_, List.getElem?_eq_getElem hoLtBoxes⟩
  have hnodePrep : (Compound.prepare boxesM P.clusterPad titles0 { nodes := nodes0, edges := edges0, slot := P.slot }).nodes[oIdx]? = some n0 := by rw [← hprep]; exact hsource0
  obtain ⟨_, hpathN⟩ := prepare_plain_path_origin boxesM P.clusterPad titles0 _ hmeta hnodePrep hb0 hboxM
  obtain ⟨origBox, horigBox, hchangeBox⟩ : ∃ origBox, inp.boxes[oIdx]? = some origBox ∧ boxM = (if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == origBox.id) then ({ origBox with role := .node } : ModelBox) else origBox) := by
    rw [List.getElem?_map] at hboxM; obtain ⟨origBox, horigBox, hchangeBox⟩ := Option.map_eq_some_iff.mp hboxM; exact ⟨origBox, horigBox, hchangeBox.symm⟩
  obtain ⟨_, _, hpathMap0⟩ := fixedSizes_path_index inp horigBox
  have hpathInp0 : n0.clusterPath = Compound.path inp.boxes origBox := by rw [hpathN, hchangeBox]; exact hpathMap0
  have hpathInp : n.clusterPath = Compound.path inp.boxes origBox := by rw [hpath0rev]; exact hpathInp0
  have hmemInp : decl ∈ Compound.path inp.boxes origBox := by rw [← hpathInp]; exact List.contains_iff_mem.mp hcontains
  have hpathEq : Compound.path inp.boxes origBox = Compound.ancestors inp.boxes inp.boxes.length origBox.parent := rfl
  have hmemAnc : decl ∈ Compound.ancestors inp.boxes inp.boxes.length origBox.parent := by rw [← hpathEq]; exact hmemInp
  obtain ⟨declBox, hboxDecl, hroleDecl, hnfDecl⟩ := c8aDM_path_member_group_nf hwf hfp inp.boxes.length origBox (List.mem_of_getElem? horigBox) hmemAnc
  have hdeclLt : decl < lines.length := by have hi := (List.getElem?_eq_some_iff.mp hboxDecl).1; omega
  have hlenBoxesM : boxesM.length = inp.boxes.length := by simp [boxesM]
  have hdeclLtM : decl < boxesM.length := by omega
  have hboxDeclM : boxesM[decl]? = some declBox := by simp [boxesM, hboxDecl, hnfDecl]
  obtain ⟨top0, bottom0, htop0, hbotmem, htopBorder, hbotBorder, htopDecl, hbotDecl, _, _, _, _⟩ := measuredGraph_paired_markers h0 hdeclLt hboxDeclM hroleDecl
  obtain ⟨top, htoplook, htopbord, htoppath, htopdecl⟩ := exactGraph_node_key h htop0
  obtain ⟨ib, hib⟩ := List.mem_iff_getElem?.mp hbotmem
  obtain ⟨bot, hbotlook, hbotbord, hbotpath, hbotdecl⟩ := exactGraph_node_key h hib
  have htb : top.border = -2 := by rw [htopbord]; exact htopBorder
  have hbb : bot.border = 2 := by rw [hbotbord]; exact hbotBorder
  have htd : top.decl = decl := by rw [htopdecl, htopDecl]
  have hbotdeclEq : bot.decl = decl := by rw [hbotdecl, hbotDecl]
  have hzipTop : (top, decl) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr htoplook
  have hmemZip : (n, oIdx) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hsource
  have hbotZip : (bot, ib) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hbotlook
  have hbotPred : (fun entry : Node × Nat => entry.1.border == 2 && entry.1.decl == top.decl) (bot, ib) = true := by simp [hbb, hbotdeclEq, htd]
  obtain ⟨bottomG, hfindG⟩ : ∃ bottomG : Node × Nat, (graph.nodes.zipIdx.find? fun entry => entry.1.border == 2 && entry.1.decl == top.decl) = some bottomG := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(bot, ib), hbotZip, hbotPred⟩)
  have hinside : n.clusterPath.contains top.decl = true := by rw [htd]; exact hcontains
  obtain ⟨he1, _⟩ := compound_member_constraint_edges hzipTop htb hfindG hmemZip hb hinside
  have hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph, e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := X_exactConstraintsBounded h0 h hlines
  obtain ⟨c, hcMem, hcTail, hcHead⟩ := components_edge_endpoints hbd (List.mem_append_right _ he1)
  have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcHead hoIn
  have hdeclInComp : decl ∈ comp := by rw [← hcEq]; exact hcTail
  have hmemCg : top ∈ (componentGraph graph comp).nodes := by apply List.mem_map.mpr ⟨decl, hdeclInComp, by rw [List.getD_eq_getElem?_getD, htoplook, Option.getD_some]⟩
  obtain ⟨u, hu⟩ := List.mem_iff_getElem?.mp hmemCg
  have hcand : (componentCandidate graph comp candidate).nodes[u]? = some top := by rw [componentCandidate_nodes]; exact hu
  exact ⟨u, top, hcand, htb, htd⟩

private theorem c8aDM_bottomToTop {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel} (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) (idx : Nat) (n : Node) (decl : Nat)
    (hn : (componentCandidate graph comp candidate).nodes[idx]? = some n)
    (hb : n.border = 2) (hcontains : n.clusterPath.contains decl = true) :
    ∃ (u : Nat) (uNode : Node), (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧ uNode.border = -2 ∧ uNode.decl = decl := by
  obtain ⟨t, hfind⟩ := X_componentRun_cg_top_of_bottom h0 h hlines hcomp hn hb
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨htBorder, htPath⟩ := hpred
  have htMem : t ∈ (componentCandidate graph comp candidate).nodes.zipIdx := List.mem_of_find?_eq_some hfind
  have htLookup : (componentCandidate graph comp candidate).nodes[t.2]? = some t.1 := List.mem_zipIdx_iff_getElem?.mp htMem
  have htContains : t.1.clusterPath.contains decl = true := by rw [htPath]; exact hcontains
  exact c8aDM_topWalk h0 h hlines hwf hfp hcomp candidate t.1.clusterPath.length t.2 t.1 decl htLookup htBorder htContains rfl

private theorem c8aDM_candidateTopExists {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel} (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) {comp : List Nat} (hcomp : comp ∈ components graph)
    (candidate : Nat) (idx : Nat) (n : Node) (decl : Nat)
    (hn : (componentCandidate graph comp candidate).nodes[idx]? = some n)
    (hcontains : n.clusterPath.contains decl = true) :
    ∃ (u : Nat) (uNode : Node), (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧ uNode.border = -2 ∧ uNode.decl = decl := by
  rcases (X_componentCandidate_marker_shape h0 h hn).1 with hb0 | hb2 | hbB
  · exact c8aDM_plainToTop h0 h hlines hwf hfp hcomp candidate idx n decl hn hb0 hcontains
  · exact c8aDM_topWalk h0 h hlines hwf hfp hcomp candidate n.clusterPath.length idx n decl hn hb2 hcontains rfl
  · exact c8aDM_bottomToTop h0 h hlines hwf hfp hcomp candidate idx n decl hn hbB hcontains

private theorem c8aDM_nonproxy {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by rw [← hdrop]; rfl
  obtain ⟨record, coordinate⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

private theorem c8aDM_fbs {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.dummy = nvp.dummy ∧ nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', hd', hb', hh'⟩ := (proxyWidths_rel hproxy).2.2.2.2.1 v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [← hdrop]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  refine ⟨run.coordinateProper.nodes[v], hcadr, ?_, ?_, ?_, ?_⟩
  · exact hd'.symm.trans (congrArg ProperNode.dummy hnde)
  · have h1 : nd'.node.border = (run.coordinateProper.nodes[v]).node.border := hb'
    have h2 : nd'.node.border = nvp.node.border := congrArg (fun n => n.node.border) hnde
    exact h1.symm.trans h2
  · have h1 : nd'.node.h = (run.coordinateProper.nodes[v]).node.h := hh'
    have h2 : nd'.node.h = nvp.node.h := congrArg (fun n => n.node.h) hnde
    exact h1.symm.trans h2
  · intro hnp
    obtain ⟨hfull, -⟩ := c8aDM_nonproxy hrun hcadr hnp
    have := Option.some.inj (hrec.symm.trans hfull)
    rw [← this]

private theorem c8aDM_coord0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := sizeProperPortsX_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

private theorem c8aDM_coord_lookupX (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases c8aDM_coord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · have hpath : m.dummy = false → nd.node.clusterPath = m.node.clusterPath := by
      intro hf
      have hfalse : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd hfalse]
      exact h3
    have hh0 : (nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0 := by
      intro hbd
      rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
    exact Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, hpath, hh0⟩
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · have hpath3 : q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath := by
      intro hf
      have hfalse : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd hfalse]
      exact h3
    exact Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, hpath3⟩)

private theorem c8aDM_pc_plain {P : Params} {exact : List Nat} {cg : Graph}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hd : nd.dummy = true) : nd.node.border = 0 := by
  rcases c8aDM_coord_lookupX P exact labeled h with
    ⟨m, hm, h1, h2, _, _⟩ | ⟨h1, _⟩ | ⟨i, q, hq, _, h1, h2, _⟩
  · rcases hK v m hm with ⟨n, _, hmd, _, _⟩ | ⟨_, hb, _⟩
    · rw [h1] at hd; rw [hmd] at hd; exact absurd hd (by decide)
    · rw [h2, hb]
  · rw [h1] at hd; exact absurd hd (by decide)
  · obtain ⟨hs, hb⟩ := titleNodes_spec hq
    have hk := sizeProperPortsX_key P exact labeled q.2
    rw [hs] at hk
    cases hp : labeled.nodes[q.2]? with
    | none => simp [hp] at hk
    | some mp =>
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hk1, hk2, _⟩ := hk
      rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
      · rw [h1, hk1, hmd] at hd; exact absurd hd (by decide)
      · rw [hk2] at hb
        rw [hb'] at hb
        exact absurd hb (by decide)

private theorem c8aDM_dummyEnds {prepared : Proper} {v : Nat} {nvc : ProperNode} {decl : Nat}
    (hnc : (materializeDummyPaths prepared).nodes[v]? = some nvc)
    (hdum : nvc.dummy = true)
    (hcontain : nvc.node.clusterPath.contains decl = true) :
    ∃ (head last : Nat),
      decl ∈ (prepared.nodes.getD head default).node.clusterPath ∧
      decl ∈ (prepared.nodes.getD last default).node.clusterPath := by
  obtain ⟨m, hm, hdm, _, _, _⟩ := materialize_lookup prepared hnc
  have hmDum : m.dummy = true := hdm.symm.trans hdum
  have hpathEq : nvc.node.clusterPath = OrderImpl.nodePath prepared v := by
    unfold materializeDummyPaths at hnc
    simp only [List.getElem?_map, List.getElem?_zipIdx, hm, Option.map_some] at hnc
    have hnd := Option.some.inj hnc
    simp only [hmDum, ↓reduceIte] at hnd
    have hcl := congrArg Node.clusterPath (congrArg ProperNode.node hnd)
    simpa using hcl.symm
  have hmem : decl ∈ OrderImpl.nodePath prepared v := by
    rw [← hpathEq]; exact List.contains_iff_mem.mp hcontain
  have hget : prepared.nodes.getD v default = m := by
    simp [List.getD_eq_getElem?_getD, hm]
  unfold OrderImpl.nodePath at hmem
  simp only [hget, hmDum] at hmem
  simp only [Bool.not_true] at hmem
  cases hfind : prepared.chains.find? (fun members => members.contains v) with
  | none =>
    simp only [hfind] at hmem
    simp at hmem
  | some chain =>
    simp only [hfind] at hmem
    obtain ⟨hl, hr⟩ := commonPath_member_both _ _ hmem
    exact ⟨chain.headD v, chain.getLastD v, hl, hr⟩

private theorem c8aDM_preparedTop {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel} (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {labeled prepared : Proper}
    (hprepEq : prepared = clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)) P.clusterBorderW))
    (hk : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)))
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩)
    {head decl : Nat}
    (hcontainHead : decl ∈ (prepared.nodes.getD head default).node.clusterPath) :
    ∃ (u : Nat) (uNode : Node), (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧ uNode.border = -2 ∧ uNode.decl = decl := by
  have hne : (prepared.nodes.getD head default).node.clusterPath ≠ [] :=
    List.ne_nil_of_mem hcontainHead
  have hdefaultPath : (default : ProperNode).node.clusterPath = [] := rfl
  have hlt : head < prepared.nodes.length := by
    by_cases hlt : head < prepared.nodes.length
    · exact hlt
    · have hle : prepared.nodes.length ≤ head := Nat.le_of_not_gt hlt
      have hgetD : prepared.nodes.getD head default = default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rw [hgetD] at hcontainHead
      rw [hdefaultPath] at hcontainHead
      simp at hcontainHead
  obtain ⟨ep, hepGet⟩ : ∃ ep, prepared.nodes[head]? = some ep :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hgetDEq : prepared.nodes.getD head default = ep := by
    simp [List.getD_eq_getElem?_getD, hepGet]
  have hcontainEp : ep.node.clusterPath.contains decl = true := by
    rw [hgetDEq] at hcontainHead
    exact List.contains_iff_mem.mpr hcontainHead
  have hep : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
      P.clusterBorderW)).nodes[head]? = some ep := by
    rw [← hprepEq]; exact hepGet
  rcases c8aDM_coord0_lookup P (exactDecls exactIds inp) labeled hep with
    ⟨m, hm, _, _, hpathEq, _⟩ | ⟨hdumEp, hbSide⟩ | ⟨i, q, hq, hv, _, hbT, hpathT⟩
  · have hcontM : m.node.clusterPath.contains decl = true := by
      rw [← hpathEq]; exact hcontainEp
    have hmemM : decl ∈ m.node.clusterPath := List.contains_iff_mem.mp hcontM
    rcases hk head m hm with ⟨n, hn, _, _, hpN⟩ | ⟨hdT, hb0, hpathNil⟩
    · have hcontN : n.clusterPath.contains decl = true := by
        rw [← hpN]; exact hcontM
      exact c8aDM_candidateTopExists h0 h hlines hwf hfp hcomp candidate head n decl hn hcontN
    · rw [hpathNil] at hmemM
      simp at hmemM
  · have hepDumF : ep.dummy = false := hdumEp
    obtain ⟨ndc, hndc, _⟩ := materialize_exists prepared hepGet
    obtain ⟨m0, hm0, _, _, _, hndEq⟩ := materialize_lookup prepared hndc
    have hm0eq : m0 = ep := Option.some.inj (hm0.symm.trans hepGet)
    have hm0DumF : m0.dummy = false := by rw [hm0eq]; exact hepDumF
    have hndcEq : ndc = ep := by
      have h1 := hndEq hm0DumF
      rw [hm0eq] at h1
      exact h1
    have hndcBorder : ndc.node.border = -1 ∨ ndc.node.border = 1 := by
      rw [hndcEq]; exact hbSide
    have hndcContain : ndc.node.clusterPath.contains decl = true := by
      rw [hndcEq]; exact hcontainEp
    have hcoordEq : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes =
        (materializeDummyPaths prepared).nodes := by
      unfold coordinateGraphX
      rw [← hprepEq]
    have hndcL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[head]? = some ndc := by
      rw [hcoordEq]; exact hndc
    obtain ⟨top, htopMem, bottom, hfindB, hpathEqSide, _, _, _⟩ :=
      addClusterBorders_side_rank_bounds (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)) P.clusterBorderW hready
        (X_side_original hready hndcL hndcBorder) hndcBorder
    have htopGet : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? = some top.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
    have htopBorder : top.1.node.border = -2 := by
      have hcond := (List.mem_filter.mp htopMem).2
      simpa using hcond
    obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
      X_titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
    have htopCgBorder : topOrig.border = -2 := htopBorderEq.symm.trans htopBorder
    have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
      rw [htopRecord]; exact (titleF_keys _).2.2.1
    have hcontOrig : topOrig.clusterPath.contains decl = true := by
      have h1 : top.1.node.clusterPath.contains decl = true := by
        rw [← hpathEqSide]; exact hndcContain
      rw [← htopPath]; exact h1
    exact c8aDM_topWalk h0 h hlines hwf hfp hcomp candidate topOrig.clusterPath.length top.2 topOrig decl htopCg htopCgBorder hcontOrig rfl
  · have hcontQ : q.1.node.clusterPath.contains decl = true := by
      rw [← hpathT]; exact hcontainEp
    have hmemQ : decl ∈ q.1.node.clusterPath := List.contains_iff_mem.mp hcontQ
    obtain ⟨hsized, hsizedBorder⟩ := titleNodes_spec hq
    obtain ⟨original, horiginal, _, _, hsourcePath⟩ :=
      X_sizeProperPorts_node_origin P (exactDecls exactIds inp) labeled hsized
    have hcontOrig : original.node.clusterPath.contains decl = true := by
      rw [← hsourcePath]; exact hcontQ
    have hmemOrig : decl ∈ original.node.clusterPath := List.contains_iff_mem.mp hcontOrig
    rcases hk q.2 original horiginal with ⟨n, hn, _, _, hpN⟩ | ⟨hdT, hb0, hpathNil⟩
    · have hcontN : n.clusterPath.contains decl = true := by
        rw [← hpN]; exact hcontOrig
      exact c8aDM_candidateTopExists h0 h hlines hwf hfp hcomp candidate q.2 n decl hn hcontN
    · rw [hpathNil] at hmemOrig
      simp at hmemOrig

/-- Dummy lookup holds: every executed proper dummy whose path carries a declaration finds its marker. -/
theorem c8aTL_topLookupDummy_holds (exactIds : List String) : C8aTL_TopLookupDummy exactIds := by
  intro P inp o lines measured graph0 graph h0 h hlines hwf hfp comp hcomp candidate run labels orderOptions hrun decl low lowNd hlow hdum hcontainLow
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ := X_cg_run_bundle h0 h hcomp hrun
  obtain ⟨nvc, hnc, hdumEq, hborderEq, hhEq, hpathImp⟩ := c8aDM_fbs hrun hlow
  have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[low]? = some nvc := by rw [hc]; exact hnc
  have hdumNvc : nvc.dummy = true := hdumEq.trans hdum
  have hborder0 : nvc.node.border = 0 := c8aDM_pc_plain hk hncL hdumNvc
  have hnp : ¬ (nvc.node.border = -2 ∨ nvc.node.border = 2) := by rw [hborder0]; decide
  have hpathEq : nvc.node.clusterPath = lowNd.node.clusterPath := hpathImp hnp
  have hcontainNvc : nvc.node.clusterPath.contains decl = true := by rw [hpathEq]; exact hcontainLow
  have hmat : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)) P.clusterBorderW))).nodes[low]? = some nvc := hncL
  obtain ⟨head, last, hhead, hlast⟩ := c8aDM_dummyEnds hmat hdumNvc hcontainNvc
  exact c8aDM_preparedTop h0 h hlines hwf hfp hcomp rfl hk hready hrecords hhead

/-- Closed top lookup with no premise. -/
theorem c8aR_topLookup_closed (exactIds : List String) : C8aR_TopLookup exactIds :=
  c8aR_topLookup_holds exactIds (c8aTL_topLookupDummy_holds exactIds)

/-- Closed anchor cover with no premise. -/
theorem XSc8a_anchorCover_closed' (exactIds : List String) :
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
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels orderOptions = .ok run →
    ∀ {decl : Nat} {low high : Nat} {lowNd highNd : ProperNode},
    run.proper.nodes[low]? = some lowNd →
    lowNd.node.clusterPath.contains decl = true →
    run.proper.nodes[high]? = some highNd →
    highNd.node.clusterPath.contains decl = true →
    ∃ (labeled : Proper), coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper ∧ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.length = (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank.length ∧ ∃ (top bottom : ProperNode × Nat), top ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧ top.1.node.border = -2 ∧ top.1.node.clusterPath.getLast? = some decl ∧ ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry => entry.1.node.border == 2 && entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧ (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat ≤ (rk run.proper.rank low).toNat ∧ (rk run.proper.rank high).toNat ≤ (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2).toNat :=
  XSc8a_anchorCover_closed exactIds (c8aTL_topLookupDummy_holds exactIds)

end PipelineImpl
end Layered
end Elegant
