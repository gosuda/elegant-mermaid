import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.ChildFrameStrictRankProof
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.DummyChainRankProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ## Prefix helpers (copies of private lemmas in `GroupTopRankResidualsProof`)

Copies are required because private lemmas cannot be imported. -/

/-- A list prefix take is a prefix. -/
private theorem desc_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

/-- A prefix is the take of its length. -/
private theorem desc_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

 /-- Of two prefixes of one list, the shorter is a prefix of the longer. -/
private theorem desc_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := desc_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact desc_take_is_prefix q p.length

/-- Mutual prefixes are equal. -/
private theorem desc_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := desc_prefix_take_eq h1
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
 
 /-- A strict prefix is strictly shorter. -/
 private theorem desc_prefix_length_lt {α : Type} {p s : List α}
     (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p := desc_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (desc_prefix_antisymm hp h2) hne
 
/-- Dropping the last element is a prefix. -/
private theorem desc_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

/-- Executed proper rank equals coordinate rank (copy of the private
`StrictMemberFrameProof.run_rank_eq_coordinate`). -/
private theorem desc_rank_eq_coordinate {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

/-- A cluster path ending in `d` has last element `d`
(copy of the private `GroupTopRankResidualsProof.cg_path_last`). -/
private theorem desc_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

/-! ## Scope helpers (copies of private lemmas in `GroupTopRankResidualsProof`) -/

/-- Candidate `-2` node path source in input boxes (copy of the private
`GroupTopRankResidualsProof.cg_group_box`). -/
private theorem desc_group_box {P : Params} {inp : Input} {o : Options}
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

/-- Scope prefix: a marker whose cluster path contains a group top's
declaration extends that top's cluster path (copy of the private
`GroupTopRankResidualsProof.cg_scope_prefix`). -/
private theorem desc_scope_prefix {inp : Input} {o : Options}
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

/-- Same-path group tops share their candidate index (copy of the private
`GroupTopRankResidualsProof.cg_top_unique`). -/
private theorem desc_top_unique {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbA : na.border = -2) (hbB : nb.border = -2)
    (hpath : na.clusterPath = nb.clusterPath) : a = b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := desc_group_box hgraph ha hbA
    exact desc_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := desc_group_box hgraph hb hbB
    exact desc_path_last hpathB
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

/-! ## Transitive group-top rank bound (non-strict copy + strict wrapper) -/

/-- Transitive group-top rank bound: a group top ranks at or below every nested
group top whose cluster path extends its own (copy of the private
`GroupTopRankResidualsProof.cg_nested_top_rank`). -/
private theorem desc_chain_le {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr) :
    ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node,
      (componentCandidate graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.clusterPath <+: nb.clusterPath →
      nb.clusterPath.length - na.clusterPath.length = delta →
      rk rr.ranks a ≤ rk rr.ranks b := by
  have hparEx := candidate_parent_top_exists hgraph hlines hwf hfp hcomp candidate
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ha hbA hb hbB hpre hdelta
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := desc_top_unique hgraph hcomp ha hb hbA hbB heq
      subst hab
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        desc_prefix_length_lt hpre heq
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
        desc_prefix_of_common_prefix hpre (huPath ▸ desc_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      have hIH := ih _ hdeltaU a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
      obtain ⟨bbot, hbbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp hb hbB
      obtain ⟨ubot, hubot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
      have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
      have hparent : (u.1, u.2) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr huLookup
      have hchild : (nb, b) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr hb
      have hinterv := ranked_compound_child_interval hrr hparent huBorder hubot
        hchild hbB hpathUB hbbot
      have hpleft : ((u.1, u.2)).2 = u.2 := rfl
      have hpright : ((nb, b)).2 = b := rfl
      rw [hpleft, hpright] at hinterv
      omega

/-- Strict transitive group-top rank bound: distinct declarations make the
prefix strict, so one direct child edge contributes its unit gap. -/
private theorem desc_chain_strict {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr)
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hbA : na.border = -2)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbB : nb.border = -2)
    (hne : na.decl ≠ nb.decl)
    (hpre : na.clusterPath <+: nb.clusterPath) :
    rk rr.ranks a + 1 ≤ rk rr.ranks b := by
  have hparEx := candidate_parent_top_exists hgraph hlines hwf hfp hcomp candidate
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := desc_group_box hgraph ha hbA
    exact desc_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := desc_group_box hgraph hb hbB
    exact desc_path_last hpathB
  have hnePath : na.clusterPath ≠ nb.clusterPath := by
    intro heq
    apply hne
    have h := congrArg List.getLast? heq
    rw [hlastA, hlastB] at h
    exact Option.some.inj h
  have hlt : na.clusterPath.length < nb.clusterPath.length :=
    desc_prefix_length_lt hpre hnePath
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
  have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
  have hpreU : na.clusterPath <+: u.1.clusterPath :=
    desc_prefix_of_common_prefix hpre (huPath ▸ desc_dropLast_is_prefix nb.clusterPath) hleU
  have hchain := desc_chain_le hgraph hlines hwf hfp hcomp candidate hrr
    _ a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
  obtain ⟨bbot, hbbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp hb hbB
  obtain ⟨ubot, hubot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
  have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
  have hparent : (u.1, u.2) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr huLookup
  have hchild : (nb, b) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hb
  have hinterv := ranked_compound_child_interval hrr hparent huBorder hubot
    hchild hbB hpathUB hbbot
  have hpleft : ((u.1, u.2)).2 = u.2 := rfl
  have hpright : ((nb, b)).2 = b := rfl
  rw [hpleft, hpright] at hinterv
  omega

/-! ## Bottom marker records (copies of private lemmas in `GroupBottomBoundaryProof`) -/

/-- Candidate `border = 2` bottom marker path fact (copy of the private
`GroupBottomBoundaryProof.bottom_marker_path`). -/
private theorem desc_bottom_path {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = 2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨original, horiginal, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨box, hbox, hrole, hpath, hw, hh⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hborder
  exact ⟨by rw [hpath]; simp, by rw [hpath]; simp⟩

/-- The coordinate-graph record of a `border = 2` bottom marker (copy of the
private `GroupBottomBoundaryProof.bottom_marker_coordinate_record`). -/
private theorem desc_bottom_coordinate {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, hnodeRec, _⟩ := componentRun_ranked_node_records hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hnodeRec v nd hnode
  have hmarker := coordinateGraph_marker_record (P := P) hrec (Or.inr hgroup) rfl
  rw [hc] at hmarker
  have hb : (clearF (titleF ⟨nd, false, none, false⟩)).node.border = 2 := by
    have h1 := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [h1, (titleF_keys _).2.1]
    exact hgroup
  have hd : (clearF (titleF ⟨nd, false, none, false⟩)).dummy = false :=
    (clearF_keys _).1.trans (titleF_keys _).1
  have hp : (clearF (titleF ⟨nd, false, none, false⟩)).node.clusterPath = nd.clusterPath :=
    (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  have hh : (clearF (titleF ⟨nd, false, none, false⟩)).node.h = 0 :=
    (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))
  exact ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, hb, hd, hp, hh⟩

/-- The executed record of the `border = 2` bottom proxy (copy of the private
`GroupBottomBoundaryProof.bottom_marker_proper_node`). -/
private theorem desc_bottom_proper {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    componentRun_proxy_interval hrun hcoord (Or.inr hb)
  have hh : RouteImpl.nodeH run.proper v = 0 := by
    simp only [RouteImpl.nodeH, hproper]
    exact hcoordH
  exact ⟨_, hproper, rfl, hh⟩
/-- Fold invariant: a lower bound on `minY` survives the hull fold. -/
private theorem desc_foldl_minY_le (rects : List Rect) (b : Bounds) (lo : Int)
    (hb : lo ≤ b.minY) (hall : ∀ r ∈ rects, lo ≤ r.y) :
    lo ≤ ((rects.foldl fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY := by
  induction rects generalizing b with
  | nil => simpa using hb
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · show lo ≤ min b.minY first.y
      have h1 := hb
      have h2 := hall first (by simp)
      omega
    · intro r hr
      exact hall r (List.mem_cons_of_mem _ hr)
/-- Non-strict hull minimum: every element at or above `lo` puts the hull
minimum at or above `lo`. -/
private theorem desc_minY_of_all_le (rects : List Rect) (lo : Int)
    (hall : ∀ r ∈ rects, lo ≤ r.y) (hne : rects ≠ []) :
    lo ≤ (boundsOf rects []).minY := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    unfold boundsOf
    dsimp only
    exact desc_foldl_minY_le (first :: rest) _ lo (hall first (by simp)) hall

/-! ## Executed descendant disjointness -/

/-- Case (2b-desc), executed: a descendant-group position (path contains the
title group, distinct declarations, not a plain member) is disjoint from the
transported caption. The caption lies in its top band
(`captionInTopBand_executed`); the descendant position ranks strictly below
the title rank (transitive child-interval chain), so the band gap
(`rankAxis_band_top_strict`) separates them vertically. -/
theorem captionMemberDescDisjoint_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) :
    CaptionMemberDescDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp := by
  intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hpath hnonplain hframe
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hposLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hfn).1
  obtain ⟨rr, _, hrr, hc, _, hranks, _, hshape⟩ :=
    rankSource_of_componentRun execution.graph_eq hcomp hrun
  have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
    have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hindexLt
    rw [hc] at h2
    exact h2
  have rEqT := desc_rank_eq_coordinate hrun i
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, hry, _, _⟩ :=
    componentRun_spec hrun
  have hindexLen : i < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun i hindexLt
  have hposLen : pos < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun pos hposLt
  have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
  rw [rEqT] at hlyT hnnT
  have hcap := (captionInTopBand_executed execution hcomp hrun hmem hnode hborder).2
  have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
    simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
  rw [hltTget] at hcap
  have hmemberGet : (componentCandidate execution.graph comp candidate).nodes.getD pos default =
      fNode := by
    simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
  by_cases hfb : fNode.border = -2
  · obtain ⟨tbox, hboxT, hpathT⟩ := desc_group_box execution.graph_eq hnode hborder
    obtain ⟨fbox, hboxF, hpathF⟩ := desc_group_box execution.graph_eq hfn hfb
    have hpre : tNode.clusterPath <+: fNode.clusterPath :=
      desc_scope_prefix hwf hboxT hpathT hboxF hpathF hpath
    have hchain := desc_chain_strict execution.graph_eq hlines hwf hframed hcomp candidate hrr
      hnode hborder hfn hfb hne hpre
    have ePos : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
      have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hposLt
      rw [hc] at h2
      exact h2
    have rEqM := desc_rank_eq_coordinate hrun pos
    obtain ⟨ltM, hlyM, _, hnnM⟩ := hcov pos hposLen
    have hnnM0 : 0 ≤ rk run.proper.rank pos := hnnM
    rw [rEqM] at hlyM hnnM
    obtain ⟨lP0, hlyP0, _, _⟩ := hcov pos hposLen
    have hltTM : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank pos).toNat := by
      have h1 := eTop
      have h2 := ePos
      have h3 := hchain
      have h4 := hnnT
      have h5 := hnnM
      omega
    have hbandTM := rankAxis_band_top_strict hry _ _ _ _ hltTM hlyT hlyM
    have htopLe := childTopRankLe_executed execution hwf hframed hcomp hrun hfn hfb
    unfold ChildTopRankLe at htopLe
    rw [hmemberGet] at htopLe
    obtain ⟨sideIndex, side, hside, _, howner⟩ :=
      execution.component_group_final_side hcomp hrun hfn hfb
    let descRects := run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains fNode.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none
    have hsideMem : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ descRects := by
      apply List.mem_filterMap.mpr
      refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
      have hmemSide : fNode.decl ∈ side.node.clusterPath := List.mem_of_getLast? howner
      simp [hmemSide]
    have hneDesc : descRects ≠ [] := by
      intro hempty
      rw [hempty] at hsideMem
      exact List.not_mem_nil hsideMem
    have hmin : run.top.getD (rk run.coordinateProper.rank pos).toNat 0 ≤
        (boundsOf descRects []).minY := by
      refine desc_minY_of_all_le _ _ ?_ hneDesc
      intro r hr
      obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hr
      split at heq
      · rename_i hcontains
        have hrectEq := Option.some.inj heq
        rw [← hrectEq]
        have hle : rk run.proper.rank pos ≤ rk run.proper.rank entry.2 :=
          htopLe entry hentry hcontains
        have hqLen : entry.2 < run.proper.nodes.length :=
          (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hentry)).1
        obtain ⟨lQ0, hlyQ0, _, hnnQ0⟩ := hcov entry.2 hqLen
        have hmonoQ : run.top.getD (rk run.proper.rank pos).toNat 0 ≤
            run.top.getD (rk run.proper.rank entry.2).toNat 0 := by
          by_cases heqR : (rk run.proper.rank pos).toNat = (rk run.proper.rank entry.2).toNat
          · rw [heqR]
            exact Int.le_refl _
          · have hltQ : (rk run.proper.rank pos).toNat < (rk run.proper.rank entry.2).toNat := by
              have h1 := hle
              have h2 := hnnQ0
              have h3 := hnnM0
              omega
            have hle2 := rankAxis_band_top_strict hry _ _ _ _ hltQ hlyP0 hlyQ0
            have hHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lP0 :=
              CoordsImpl.layerHeight_nonneg _ _
            omega
        have hbandLoQ := (fbs_run_node_band hrun entry.2 hqLen).1
        have hYq : (Labels.rectAt run.proper run.xs run.ys entry.2).y =
            run.ys.getD entry.2 0 := rfl
        rw [hYq, ← rEqM]
        have h1 := hmonoQ
        have h2 := hbandLoQ
        omega
      · cases heq
    have hframeY : g0.y = (boundsOf descRects []).minY := by
      rw [← hframe]
      simp only [descRects, frameRect, hmemberGet, hfb,
        show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [← hframeY] at hmin
    unfold Disjoint
    intro hcon
    obtain ⟨-, hy⟩ := hcon
    omega
  · have hb2 : fNode.border = 2 := by
      have hshapeB := (hshape pos fNode hfn).1
      rcases hshapeB with h0 | hm2 | h2
      · exact absurd h0 hnonplain
      · exact absurd hm2 hfb
      · exact h2
    obtain ⟨t, ht⟩ := componentRun_cg_top_of_bottom execution.graph_eq hlines hcomp hfn hb2
    have htPred := List.find?_some ht
    simp only [Bool.and_eq_true, beq_iff_eq] at htPred
    obtain ⟨htBorder, htPath⟩ := htPred
    have htMem : t ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
      List.mem_of_find?_eq_some ht
    have htLookup : (componentCandidate execution.graph comp candidate).nodes[t.2]? = some t.1 :=
      List.mem_zipIdx_iff_getElem?.mp htMem
    obtain ⟨tbox, hboxT, hpathT⟩ := desc_group_box execution.graph_eq hnode hborder
    obtain ⟨ttbox, hboxtT, hpathtT⟩ := desc_group_box execution.graph_eq htLookup htBorder
    have hlastT : t.1.clusterPath.getLast? = some t.1.decl := desc_path_last hpathtT
    have hlastF : fNode.clusterPath.getLast? = some fNode.decl :=
      (desc_bottom_path execution.graph_eq hfn hb2).1
    have htDecl : t.1.decl = fNode.decl := by
      have hget : t.1.clusterPath.getLast? = fNode.clusterPath.getLast? :=
        congrArg List.getLast? htPath
      rw [hlastT, hlastF] at hget
      exact Option.some.inj hget
    have hneT : tNode.decl ≠ t.1.decl := by
      rw [htDecl]
      exact hne
    have hcontainsT : t.1.clusterPath.contains tNode.decl = true := by
      rw [htPath]
      exact hpath
    have hpreT : tNode.clusterPath <+: t.1.clusterPath :=
      desc_scope_prefix hwf hboxT hpathT hboxtT hpathtT hcontainsT
    have hchainT := desc_chain_strict execution.graph_eq hlines hwf hframed hcomp candidate hrr
      hnode hborder htLookup htBorder hneT hpreT
    obtain ⟨coord, hcoord, hcoordB, _, hcoordP, hcoordH⟩ :=
      desc_bottom_coordinate hrun hfn hb2
    obtain ⟨bprop, hbprop, hbpropP, _⟩ :=
      desc_bottom_proper hrun hcoord hcoordB hcoordH
    have hbproperD : run.proper.nodes.getD pos default = bprop := by
      simp only [List.getD_eq_getElem?_getD, hbprop, Option.getD_some]
    have htLt : t.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp htLookup).1
    have hcontainsP : (run.proper.nodes.getD pos default).node.clusterPath.contains
        t.1.decl = true := by
      rw [hbproperD, hbpropP, hcoordP, htDecl]
      exact (desc_bottom_path execution.graph_eq hfn hb2).2
    have hclose := groupTopSubtreeRankProper' execution.graph_eq hlines hwf hframed hcomp hrun
      htLookup htBorder htLt hposLen hcontainsP
    have etT : rk run.coordinateProper.rank t.2 = rk rr.ranks t.2 := by
      have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks htLt
      rw [hc] at h2
      exact h2
    have rEqN := desc_rank_eq_coordinate hrun t.2
    have htLen : t.2 < run.proper.nodes.length :=
      componentRun_original_nodes_covered hrun t.2 htLt
    obtain ⟨ltN, hlyN, _, hnnN⟩ := hcov t.2 htLen
    rw [rEqN] at hlyN hnnN
    have hltTN : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank t.2).toNat := by
      have h1 := eTop
      have h2 := etT
      have h3 := hchainT
      have h4 := hnnT
      have h5 := hnnN
      omega
    have hbandTN := rankAxis_band_top_strict hry _ _ _ _ hltTN hlyT hlyN
    obtain ⟨lP0B, hlyP0B, _, hnnP0B⟩ := hcov t.2 htLen
    obtain ⟨lQ0B, hlyQ0B, _, hnnQ0B⟩ := hcov pos hposLen
    have hmono : run.top.getD (rk run.proper.rank t.2).toNat 0 ≤
        run.top.getD (rk run.proper.rank pos).toNat 0 := by
      by_cases heqR : (rk run.proper.rank t.2).toNat = (rk run.proper.rank pos).toNat
      · rw [heqR]
        exact Int.le_refl _
      · have hltQ : (rk run.proper.rank t.2).toNat < (rk run.proper.rank pos).toNat := by
          have h1 := hclose
          have h2 := hnnP0B
          have h3 := hnnQ0B
          omega
        have hle2 := rankAxis_band_top_strict hry _ _ _ _ hltQ hlyP0B hlyQ0B
        have hHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lP0B :=
          CoordsImpl.layerHeight_nonneg _ _
        omega
    have hbandLo := (fbs_run_node_band hrun pos hposLen).1
    have hb : (fNode.border != -2) = true := by
      simp only [bne_iff_ne]
      exact hfb
    have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos =
        nodeRect (componentCandidate execution.graph comp candidate) run pos := by
      unfold frameRect
      simp only [hmemberGet, hb, ↓reduceIte]
    have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
        run.ys.getD pos 0 := rfl
    have hbelow : (transportCaption execution.params o execution.lines comp i stored0).y +
        (transportCaption execution.params o execution.lines comp i stored0).h ≤
        run.ys.getD pos 0 := by
      have h1 := hcap
      have h2 := hbandTN
      rw [rEqN] at hmono
      have h3 := hmono
      have h4 := hbandLo
      omega
    unfold Disjoint
    intro hcon
    obtain ⟨-, hy⟩ := hcon
    rw [← hframe, hfr, hgy] at hy
    omega

end Elegant.Layered.PipelineImpl
