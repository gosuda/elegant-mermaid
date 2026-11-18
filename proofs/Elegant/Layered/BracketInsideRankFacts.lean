import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BottomClearanceInside
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.BottomSeamsRank

set_option autoImplicit false

/-!
# Rank seams: plain members rank strictly below their group's bottom proxy

`plainMemberRankLtProxy` (`BottomClearanceInside.lean`) holds for every
measured graph whose line list covers the input boxes: a non-dummy border-`0`
node whose cluster path contains the declaration `d` that ends a bottom
proxy's cluster path ranks strictly below that proxy.

The proof rides the public transports: `rankSource_of_componentRun` (ranking
result, labeled proper graph, rank records, marker shape),
`ranked_compound_member_interval` (the member bracket constraints of the
ranking graph), `componentRun_cg_top_of_bottom` (the paired `border = -2` top
marker of a candidate bottom), and `prepared_coordinate_original_rk` (rank
transport from the ranking to the coordinate graph).

The one missing ingredient is bottom-marker uniqueness — at most one
`border = 2` node per declaration, at one index — which the repository only
has privately (`RouteProxyStart.prepare_bottom_unique`).  It is re-derived
here from the public construction lemmas: `markNodes_eq` splits the prepared
node list into the mapped source nodes (which `markOne` never gives border
`2`) and `markExtras`, whose entries are literal records determined by their
declaration (`markExtras_eq_map`), and `nodup_map_inj_aux` pins the index.

The height clause `dummyInsideSameRankFalse` is analyzed in the final report.
-/

namespace Elegant.Layered.PipelineImpl

/-! ### Bottom-marker uniqueness -/

/-- `markOne` never produces a bottom marker: the group branch writes
`border := -2` and the other branches keep the source node's border. -/
theorem markOne_border_ne_two {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {q : Node × Nat} (hq : q.1.border ≠ 2) :
    (markOne boxes pad titles q).border ≠ 2 := by
  unfold markOne
  split
  · exact hq
  · split
    · exact (show (-2 : Int) ≠ 2 by decide)
    · exact hq

/-- Graph-level bottom-marker uniqueness: at most one `border = 2` node per
declaration, and it sits at one index of the prepared node list. -/
theorem measuredGraph_bottom_pair_eq {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {e f : Node × Nat} (he : e ∈ graph.nodes.zipIdx) (hf : f ∈ graph.nodes.zipIdx)
    (hbe : e.1.border = 2) (hbf : f.1.border = 2) (hde : e.1.decl = f.1.decl) :
    e = f := by
  obtain ⟨nodes0, edges0, titles0, hgraphEq, hlen0, hmeta⟩ :=
    measuredGraph_prepared_source hgraph
  let boxesD : List ModelBox := (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
  have hsplit : graph.nodes =
      (nodes0.zipIdx.map (markOne boxesD P.clusterPad titles0)) ++ markExtras boxesD := by
    rw [hgraphEq, Compound.prepare_nodes, markNodes_eq]
  have hplain0 : ∀ (k : Nat) (m : Node), nodes0[k]? = some m → m.border = 0 :=
    fun k m hk => (hmeta k m hk).2
  have hmarkBorder : ∀ q ∈ nodes0.zipIdx, (markOne boxesD P.clusterPad titles0 q).border ≠ 2 := by
    intro q hq
    have hlook : nodes0[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
    have hzero : q.1.border = 0 := hplain0 q.2 q.1 hlook
    exact markOne_border_ne_two (by rw [hzero]; decide)
  have hextra : ∀ n ∈ graph.nodes, n.border = 2 → n ∈ markExtras boxesD := by
    intro n hn hb
    rw [hsplit] at hn
    rcases List.mem_append.mp hn with hm | hex
    · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hm
      rw [← heq] at hb
      exact absurd hb (hmarkBorder q hq)
    · exact hex
  rw [markExtras_eq_map] at hextra
  obtain ⟨qE, hqE, hlitE⟩ := List.mem_map.mp
    (hextra e.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)) hbe)
  obtain ⟨qF, hqF, hlitF⟩ := List.mem_map.mp
    (hextra f.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hf)) hbf)
  have hdeclE : e.1.decl = qE.2 := by rw [← hlitE]
  have hdeclF : f.1.decl = qF.2 := by rw [← hlitF]
  have hq2 : qE.2 = qF.2 := (hdeclE.symm.trans hde).trans hdeclF
  have hqElook : boxesD[qE.2]? = some qE.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hqE).1
  have hqFlook : boxesD[qF.2]? = some qF.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hqF).1
  have hqE2F : boxesD[qE.2]? = some qF.1 := by rw [hq2]; exact hqFlook
  have hqEF : qE = qF := Prod.ext (Option.some.inj (hqElook.symm.trans hqE2F)) hq2
  have hval : e.1 = f.1 := by rw [← hlitE, ← hlitF, hqEF]
  have hlenMap : (nodes0.zipIdx.map (markOne boxesD P.clusterPad titles0)).length =
      nodes0.length := by
    simp only [List.length_map, List.length_zipIdx]
  have hlookupE : graph.nodes[e.2]? = some e.1 := List.mem_zipIdx_iff_getElem?.mp he
  have hlookupF : graph.nodes[f.2]? = some f.1 := List.mem_zipIdx_iff_getElem?.mp hf
  rw [← hval] at hlookupF
  have hindexCase : ∀ (k : Nat), graph.nodes[k]? = some e.1 →
      ∃ j : Nat, j < (markExtras boxesD).length ∧
        (markExtras boxesD)[j]? = some e.1 ∧ nodes0.length + j = k := by
    intro k hk
    rw [hsplit] at hk
    by_cases hlt : k < nodes0.length
    · exfalso
      rw [List.getElem?_append_left (by rw [hlenMap]; exact hlt)] at hk
      rw [List.getElem?_map, Option.map_eq_some_iff] at hk
      obtain ⟨q, hq, heq⟩ := hk
      rw [← heq] at hbe
      exact absurd hbe (hmarkBorder q (List.mem_of_getElem? hq))
    · refine ⟨k - nodes0.length, ?_, ?_, by omega⟩
      · rw [List.getElem?_append_right (by rw [hlenMap]; omega)] at hk
        rw [hlenMap] at hk
        exact (List.getElem?_eq_some_iff.mp hk).1
      · rw [List.getElem?_append_right (by rw [hlenMap]; omega)] at hk
        rw [hlenMap] at hk
        exact hk
  obtain ⟨jE, hjElen, hjEget, hjEpos⟩ := hindexCase e.2 hlookupE
  obtain ⟨jF, hjFlen, hjFget, hjFpos⟩ := hindexCase f.2 hlookupF
  rw [markExtras_eq_map, List.getElem?_map, Option.map_eq_some_iff] at hjEget hjFget
  obtain ⟨rE, hrEget, hrEeq⟩ := hjEget
  obtain ⟨rF, hrFget, hrFeq⟩ := hjFget
  have hrEmem : rE ∈ (boxesD.zipIdx.filter fun q => q.1.role == .group) :=
    List.mem_of_getElem? hrEget
  have hrFmem : rF ∈ (boxesD.zipIdx.filter fun q => q.1.role == .group) :=
    List.mem_of_getElem? hrFget
  have hrE2 : rE.2 = e.1.decl := by rw [← hrEeq]
  have hrF2 : rF.2 = e.1.decl := by rw [← hrFeq]
  have hrE2F : boxesD[rE.2]? = some rF.1 := by
    rw [show rE.2 = rF.2 from hrE2.trans hrF2.symm]
    exact List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hrFmem).1
  have hrEF : rE = rF := Prod.ext
    (Option.some.inj ((List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hrEmem).1).symm.trans
      hrE2F))
    (hrE2.trans hrF2.symm)
  have hzipNodup : (boxesD.zipIdx.map Prod.snd).Nodup := by
    have h2 : ∀ (l : List ModelBox) (n : Nat),
        (l.zipIdx n).map Prod.snd = List.range' n l.length := by
      intro l
      induction l with
      | nil => intro n; simp
      | cons b bs ih =>
          intro n
          simp only [List.zipIdx_cons, List.map_cons]
          rw [ih (n + 1)]
          show n :: List.range' (n + 1) bs.length = List.range' n (bs.length + 1)
          rw [List.range'_succ]
    rw [h2 boxesD 0]
    exact List.nodup_range'
  have hjij : jE = jF :=
    nodup_map_inj_aux (f := Prod.snd)
      (List.Nodup.sublist (List.Sublist.map Prod.snd List.filter_sublist) hzipNodup)
      hrEget hrFget (by rw [hrEF])
  exact Prod.ext hval (by omega)


/-- The by-declaration bottom `find?` of the component candidate returns
exactly the candidate's own bottom marker pair. -/
theorem componentCandidate_bottom_find_eq {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {i : Nat} {n : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some n)
    (hborder : n.border = 2) :
    (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
      entry.1.border == 2 && entry.1.decl == n.decl) = some (n, i) := by
  have hccLen : i < (componentCandidate graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  obtain ⟨vI, hcompI, hgraphI⟩ := componentCandidate_nonplain_source hnode (by
    rw [hborder]; decide)
  have hIzip : (n, vI) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hgraphI
  have hzipRecord :
      (componentCandidate graph comp candidate).nodes.zipIdx[i]? = some (n, i) := by
    simp only [List.getElem?_zipIdx, hnode, Option.map_some, Nat.zero_add]
  obtain ⟨hzipBound, hzipGet⟩ := List.getElem?_eq_some_iff.mp hzipRecord
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp [hborder], i, by simpa only [List.length_zipIdx] using hccLen,
    hzipGet, ?_⟩
  intro j hj
  have hjlook : (componentCandidate graph comp candidate).nodes[j]? =
      some (componentCandidate graph comp candidate).nodes[j] :=
    List.getElem?_eq_getElem (by omega)
  simp only [List.getElem_zipIdx, Bool.not_eq_eq_eq_not, Bool.not_true]

  apply Bool.eq_false_iff.mpr
  intro hmatch
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  obtain ⟨hjB, hjD⟩ := hmatch
  obtain ⟨vJ, hcompJ, hgraphJ⟩ := componentCandidate_nonplain_source hjlook (by
    rw [hjB]; decide)
  have hpairEq : ((componentCandidate graph comp candidate).nodes[j], vJ) = (n, vI) :=
    measuredGraph_bottom_pair_eq hgraph
      (List.mem_zipIdx_iff_getElem?.mpr hgraphJ) hIzip hjB hborder hjD
  have hvJ : vJ = vI := congrArg Prod.snd hpairEq
  have hji : j = i :=
    nodup_map_inj_aux (fun x => x) (by simpa using components_nodup graph comp hcomp)
      (by rw [← hvJ]; exact hcompJ) hcompI rfl
  omega

/-- `plainMemberRankLtProxy` for every measured graph whose line list covers
the input boxes.  The line-count premise is what the public transports
require (`componentRun_cg_top_of_bottom`, `measuredGraph_paired_markers`);
the executed pipeline always supplies it. -/
theorem plainMemberRankLtProxy_of_measuredGraph {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length) :
    plainMemberRankLtProxy P graph := by
  intro comp hcomp candidate run labels orderOptions hrun t v htborder hvdummy hvborder
    d hlast hcontains
  obtain ⟨rr, labeled, hrr, hcoord, hkeys, hranks, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  cases hvt : run.coordinateProper.nodes[t]? with
  | none =>
      rw [List.getD_eq_getElem?_getD, hvt, Option.getD_none] at htborder
      have hd : ((default : ProperNode).node.border : Int) = 0 := rfl
      omega
  | some ndT =>
      have htD : run.coordinateProper.nodes.getD t default = ndT := by
        simp [List.getD_eq_getElem?_getD, hvt]
      rw [htD] at htborder
      rw [htD] at hlast
      cases hvv : run.coordinateProper.nodes[v]? with
      | none =>
          rw [List.getD_eq_getElem?_getD, hvv, Option.getD_none] at hcontains
          have hnil : (default : ProperNode).node.clusterPath = [] := rfl
          rw [hnil] at hcontains
          exact absurd hcontains (by simp)
      | some ndV =>
          have hvD : run.coordinateProper.nodes.getD v default = ndV := by
            simp [List.getD_eq_getElem?_getD, hvv]
          rw [hvD] at hvdummy hvborder hcontains
          rw [← hcoord] at hvt hvv
          rcases coordinateGraph_lookup P labeled hvt with
            ⟨mt, hmt, _, hbT, hpT, _⟩ | ⟨_, hbT⟩ | ⟨_, _, _, _, _, hbT, _⟩
          · rcases hkeys t mt hmt with ⟨nT, hnT, hmdT, hnbT, hnpT⟩ | ⟨_, hmb0, _⟩
            · rcases coordinateGraph_lookup P labeled hvv with
                ⟨mv, hmv, hdV, hbV, hpV, _⟩ | ⟨_, hbV⟩ | ⟨_, _, _, _, _, hbV, _⟩
              · rcases hkeys v mv hmv with ⟨nV, hnV, hmdV, hnbV, hnpV⟩ | ⟨hmd2, _, _⟩
                · have hnTb : nT.border = 2 := by rw [← hnbT, ← hbT]; exact htborder
                  have hnVb : nV.border = 0 := by rw [← hnbV, ← hbV]; exact hvborder
                  have hpathT : ndT.node.clusterPath = nT.clusterPath :=
                    (hpT hmdT).trans hnpT
                  have hpathV : ndV.node.clusterPath = nV.clusterPath :=
                    (hpV hmdV).trans hnpV
                  obtain ⟨oT, _, hgraphT⟩ := componentCandidate_nonplain_source hnT (by
                    rw [hnTb]; decide)
                  obtain ⟨boxT, _, _, hpathBoxT, _, _⟩ :=
                    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hgraphT) hnTb
                  have hlastDecl : nT.clusterPath.getLast? = some nT.decl := by
                    rw [hpathBoxT, List.getLast?_append]; simp
                  have hdecl : nT.decl = d := by
                    have h := congrArg List.getLast? hpathT
                    rw [hlast, hlastDecl] at h
                    exact (Option.some.inj h).symm
                  obtain ⟨Tpair, hTfind⟩ :=
                    componentRun_cg_top_of_bottom hgraph hlines hcomp hnT hnTb
                  have hTpred := List.find?_some hTfind
                  simp only [Bool.and_eq_true, beq_iff_eq] at hTpred
                  obtain ⟨hTb, hTp⟩ := hTpred
                  have hTmem : Tpair ∈
                      (componentCandidate graph comp candidate).nodes.zipIdx :=
                    List.mem_of_find?_eq_some hTfind
                  have hTlook :
                      (componentCandidate graph comp candidate).nodes[Tpair.2]? =
                        some Tpair.1 :=
                    List.mem_zipIdx_iff_getElem?.mp hTmem
                  obtain ⟨oTp, _, hgraphTp⟩ := componentCandidate_nonplain_source hTlook (by
                    rw [hTb]; decide)
                  have hTpDecl : Tpair.1.decl = nT.decl :=
                    (measuredGraph_group_bottom_path_iff_decl hgraph hgraphTp hTb
                      (List.mem_of_getElem? hgraphT) hnTb |>.mp hTp.symm).symm
                  have hfind := componentCandidate_bottom_find_eq hgraph hcomp hnT hnTb
                  rw [← hTpDecl] at hfind
                  have hmemV : (nV, v) ∈
                      (componentCandidate graph comp candidate).nodes.zipIdx :=
                    List.mem_zipIdx_iff_getElem?.mpr hnV
                  have hinside : nV.clusterPath.contains Tpair.1.decl = true := by
                    rw [hTpDecl, hdecl, ← hpathV]
                    exact hcontains
                  obtain ⟨_, hinterv2⟩ := ranked_compound_member_interval hrr hTmem hTb
                    hfind hmemV hnVb hinside
                  have hvBound : v < (componentCandidate graph comp candidate).nodes.length :=
                    (List.getElem?_eq_some_iff.mp hnV).1
                  have htBound : t < (componentCandidate graph comp candidate).nodes.length :=
                    (List.getElem?_eq_some_iff.mp hnT).1
                  have hrv : rk (coordinateGraph P labeled).rank v = rk rr.ranks v :=
                    prepared_coordinate_original_rk hrr hranks hvBound
                  have hrt : rk (coordinateGraph P labeled).rank t = rk rr.ranks t :=
                    prepared_coordinate_original_rk hrr hranks htBound
                  rw [hcoord] at hrv hrt
                  have hint2 : rk rr.ranks v + 1 ≤ rk rr.ranks t := by
                    simpa using hinterv2
                  omega
                · rw [hdV, hmd2] at hvdummy; simp at hvdummy
              · omega
              · omega
            · omega
          · omega
          · omega

/-! ### The status of `dummyInsideSameRankFalse`

`dummyInsideSameRankFalse` (`BottomClearanceInside.lean:159`) is FALSE as
written, and is therefore NOT proved here.  A positive-height dummy is a
label node: `Labels.addLabelNode` does not create nodes, it resizes the
chain node of its edge at rank `tailRank + span / 2` (`span ≥ 2`), so such a
node sits at the midpoint rank of an edge whose endpoints strictly straddle
that rank.  Nothing in the constraint set keeps a bottom proxy's rank clear
of an edge midpoint: an edge from a group's last member `m` (rank `t-1`,
where the group's bottom proxy ranks `t`) to a plain node `b` that a second
member path pushes to rank `t+1` has span 2 and midpoint exactly `t`.

Witness source for the public adapter (expected ranking: `G.top=0, m=1,
G.bottom=2, j=2, b=3`, so the label of `m -->|lab| b` ranks 2, sharing
`G.bottom`'s rank with positive measured height and `dummy = true`):

```text
flowchart TD
subgraph SG [G]
  m
end
subgraph SJ [J]
  j
end
m --> j
m -->|lab| b
j --> b
```

All four hypotheses of the clause hold for `t` = `G`'s bottom proxy and
`v` = the resized chain node of `m -->|lab| b`; the conclusion `False` does
not follow.  The executed ranking is longest-path tight, so these ranks are
forced, not merely permitted; running the witness through the adapter
confirms or refutes it in one command.

The nearest true form is geometric, not rank-level: at every use site
(`BottomClearanceInside.lean:695,727,935`) the clause is applied to a node
`v` that additionally lies in the bottom proxy's layer and overlaps the
frame's x-span.  The missing executed fact is that a label node landing in a
bottom proxy's rank row is horizontally separated from that proxy's bracket
span (or that such a source is rejected); it cannot be derived from the
ranking constraints alone, as the witness shows.  Until that fact lands,
`BracketInsidePremises` must keep `dummyInsideSameRankFalse` as a named
premise instantiated from execution, or the consumer must take the
x-separation premise directly.
-/

end Elegant.Layered.PipelineImpl