import Elegant.Layered.GroupBottomBoundaryProof
import Elegant.Layered.BottomNestedRankProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Dummy-only restriction of `BottomSyntheticRankLe`: an executed edge-dummy
whose cluster path carries the outer group's declaration ranks at or below
the outer bottom proxy. The chain source
(`componentRun_dummy_path_chain_source`) puts the dummy between its endpoint
ranks, and both endpoints are originals, so this follows from the same
`bottomOrigRankLe` transport as the proved cases once the endpoint bridge is
available. Strictly simpler than the full synthetic goal: same executed-run
premises, conclusion restricted to the dummy disjunct. -/
def BottomDummyRankLe (P : Params) (graph : Graph) : Prop :=
  ∀ {inp : Input} {o : Options} {lines : List (List Measure.Line)},
  measuredGraph P inp o lines = .ok graph →
  lines.length = inp.boxes.length →
  WellFormed (inputModel inp o) →
  framedParents inp = true →
  ∀ {comp : List Nat}, comp ∈ components graph →
  ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions},
  componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run →
  ∀ {v t : Nat} {ndV ndT : Node},
  (componentCandidate graph comp candidate).nodes[v]? = some ndV →
  (componentCandidate graph comp candidate).nodes[t]? = some ndT →
  ndV.border = 2 → ndT.border = -2 → ndV.decl = ndT.decl →
  ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
  q.1.node.clusterPath.contains
    ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
  q.1.dummy = true →
  rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v

/-- From `toNat` order to `Int` order under nonnegativity. -/
private theorem toNat_le_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.toNat ≤ b.toNat) : a ≤ b := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by exact_mod_cast h
  omega
/-- Side markers: created per rank between their own top and bottom
(`coordinateGraph_side_rank_bounds`), and their own bottom is the outer
bottom or a nested one (`candidate_titled_bottom_constraint_source` plus
`BottomNestedBottomRankLe`). -/
private theorem side_marker_rank_le
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : ∀ P graph, BottomNestedBottomRankLe P graph)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hcontains : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
    (hside : q.1.node.border = -1 ∨ q.1.node.border = 1) :
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := fbs_coordinate_record hrun hqget
  have hsideC : nvc.node.border = -1 ∨ nvc.node.border = 1 := by
    rw [hborderEq]; exact hside
  have hncL : (coordinateGraph P labeled).nodes[q.2]? = some nvc := by
    rwa [← hc] at hnc
  obtain ⟨top, htopMem, bottom, hfindB, hpathEq, hnn, _, hhi⟩ :=
    coordinateGraph_side_rank_bounds hready hncL hsideC
  have htopGet : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
  have htopBorder : top.1.node.border = -2 := by
    simpa using (List.mem_filter.mp htopMem).2
  obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
    titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
  have htopCgBorder : topOrig.border = -2 := htopBorderEq.symm.trans htopBorder
  have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
    rw [htopRecord]; exact (titleF_keys _).2.2.1
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  have hnotProxy : ¬(nvc.node.border = -2 ∨ nvc.node.border = 2) := by
    rintro (h | h) <;> omega
  have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath :=
    hpathImp hnotProxy
  have htopContains : top.1.node.clusterPath.contains ndT.decl = true := by
    rw [← hpathEq, hnvcPath, ← hdeclT]; exact hcontains
  have htopOrigContains : topOrig.clusterPath.contains ndT.decl = true := by
    rw [← htopPath]; exact htopContains
  have hfindB' : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topOrig.clusterPath) = some bottom := by
    rw [← htopPath]; exact hfindB
  obtain ⟨origB, horigB, hborderB, hpathB, _, _⟩ :=
    candidate_titled_bottom_constraint_source hgraph hk hrecords htopCg
      htopCgBorder hfindB'
  have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
    rw [hpathB]; exact htopOrigContains
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) =
      some (ndV, v) := by
    rw [← hdecl]; exact componentCandidate_bottom_find_eq hgraph hcomp hvGet hbordV
  have hBle : rk run.coordinateProper.rank bottom.2 ≤
      rk run.coordinateProper.rank v := by
    by_cases hdeq : origB.decl = ndT.decl
    · have hfindBdec := componentCandidate_bottom_find_eq hgraph hcomp horigB hborderB
      rw [hdeq] at hfindBdec
      have heq := Option.some.inj (hfindBdec.symm.trans hbotFindOuter)
      have hbv : bottom.2 = v := congrArg Prod.snd heq
      rw [hbv]
      exact Int.le_refl _
    · exact hnest P graph hgraph hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
        horigB hborderB hdeq hpathBmem
  have hBcoord : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
    have hlt : bottom.2 < (componentCandidate graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp horigB).1
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranks hlt
    rw [← hc]; exact h1
  have hBtitle : rk (titleReservations (sizeProperPorts P labeled)).rank bottom.2 =
      rk rr.ranks bottom.2 :=
    (prepared_titled_original_rk (P := P) hrr hranks
      (List.getElem?_eq_some_iff.mp horigB).1).1
  have hBnn : 0 ≤ rk rr.ranks bottom.2 := rankWithBudget_rk_nonneg hrr bottom.2
  have hbotnn : 0 ≤ rk run.coordinateProper.rank bottom.2 := by
    rw [hBcoord]; exact hBnn
  have htonat : (rk (coordinateGraph P labeled).rank q.2).toNat ≤
      (rk run.coordinateProper.rank bottom.2).toNat := by
    rw [hBcoord, ← hBtitle]; exact hhi
  have hqb : rk (coordinateGraph P labeled).rank q.2 ≤
      rk run.coordinateProper.rank bottom.2 :=
    toNat_le_of_nonneg hnn hbotnn htonat
  have hq : rk run.coordinateProper.rank q.2 ≤
      rk run.coordinateProper.rank bottom.2 := by
    have hQ : rk run.coordinateProper.rank q.2 =
        rk (coordinateGraph P labeled).rank q.2 := by
      rw [hc]
    rw [hQ]; exact hqb
  exact Int.le_trans hq hBle

/-- Title copies: each copy carries its anchor's rank
(`coordinateGraph_title_rank_source`), and the anchor is an original top
bounded by `bottomOrigRankLe`. -/
private theorem title_copy_rank_le
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : ∀ P graph, BottomNestedBottomRankLe P graph)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hcontains : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
    (hb3 : q.1.node.border = 3) :
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  obtain ⟨_, labeled, _, hc, hk, hready, _, _⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (measuredGraph_shape hgraph) candidate
  have haligned : labeled.nodes.length = labeled.rank.length :=
    source_alignment_of_titled hready.2.2.2.1
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := fbs_coordinate_record hrun hqget
  have hncL : (coordinateGraph P labeled).nodes[q.2]? = some nvc := by
    rwa [← hc] at hnc
  have hb3C : nvc.node.border = 3 := by rw [hborderEq]; exact hb3
  obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath,
      htitleRank⟩ :=
    coordinateGraph_title_rank_source hk hshape haligned hncL hb3C
  have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath := by
    apply hpathImp
    rintro (h | h) <;> omega
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  have horigContains : original.node.clusterPath.contains ndT.decl = true := by
    rw [← htitlePath, hnvcPath, ← hdeclT]; exact hcontains
  rcases hk originalIndex original horiginal with
    ⟨n, hn, _, hborderN, hpathN⟩ | ⟨hdT, _, _⟩
  · have hnBorder : n.border = -2 := hborderN.symm.trans hOrigBorder
    have hncN : n.clusterPath.contains ndT.decl = true := by
      rw [← hpathN]; exact horigContains
    have hle := bottomOrigRankLe hgraph hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
      hnest hn hncN
    have hrankEq : rk run.coordinateProper.rank q.2 = rk labeled.rank originalIndex := by
      rw [← hc]; exact htitleRank
    have hlabEq : rk labeled.rank originalIndex =
        rk run.coordinateProper.rank originalIndex := by
      rw [← hc]
      have hlabLen : originalIndex < labeled.rank.length := by
        have h1 : originalIndex < labeled.nodes.length :=
          (List.getElem?_eq_some_iff.mp horiginal).1
        omega
      have hlabLook : labeled.rank[originalIndex]? = some labeled.rank[originalIndex] :=
        List.getElem?_eq_getElem hlabLen
      have htitLook := titled_rank_record (P := P) hlabLook
      have hcoordLook := coordinateGraph_titled_rank_record htitLook
      simp only [rk, List.getD_eq_getElem?_getD, hlabLook, hcoordLook,
        Option.getD_some]
    rw [hrankEq, hlabEq]; exact hle
  · rw [hdT] at hOrigReal
    simp at hOrigReal

/-- The synthetic-member rank bound: side markers and title copies by the two
lemmas above; edge dummies by the `BottomDummyRankLe` residual. -/
theorem bottomSyntheticRankLe
    (hdummy : ∀ P graph, BottomDummyRankLe P graph) :
    ∀ (P : Params) (graph : Graph), BottomSyntheticRankLe P graph := by
  intro P graph inp o lines hgraph hlines hwf hframed comp hcomp candidate run
    labels orderOptions hrun v t ndV ndT hvGet htGet hbordV hbordT hdecl q hq
    hcontains hkind
  have hnest : ∀ P graph, BottomNestedBottomRankLe P graph :=
    bottomNestedBottomRankLe
  rcases hkind with hd | hb1 | hb2 | hb3
  · exact hdummy P graph hgraph hlines hwf hframed hcomp hrun hvGet htGet hbordV
      hbordT hdecl q hq hcontains hd
  · exact side_marker_rank_le hgraph hlines hwf hframed hcomp hrun hvGet htGet
      hbordV hbordT hdecl hnest q hq hcontains (Or.inl hb1)
  · exact side_marker_rank_le hgraph hlines hwf hframed hcomp hrun hvGet htGet
      hbordV hbordT hdecl hnest q hq hcontains (Or.inr hb2)
  · exact title_copy_rank_le hgraph hlines hwf hframed hcomp hrun hvGet htGet
      hbordV hbordT hdecl hnest q hq hcontains hb3

/-- The group bottom boundary fact from the single remaining dummy residual:
`bottomSyntheticRankLe` discharges the synthetic seam with `hdummy` and the
proved `bottomNestedBottomRankLe`, and `groupBottomBoundaryFacts_executed`
closes the boundary with both seams. -/
theorem groupBottomBoundaryFacts_of_dummy
    (hdummy : ∀ P graph, BottomDummyRankLe P graph) :
    GroupBottomBoundaryFacts :=
  groupBottomBoundaryFacts_executed (bottomSyntheticRankLe hdummy)
    bottomNestedBottomRankLe

end Elegant.Layered.PipelineImpl
