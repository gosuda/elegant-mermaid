import Elegant.Layered.ExactCaptionAncestorFactsProof
import Elegant.Layered.ExactCaptionAncestorsLocalProof
import Elegant.Layered.ExactCaptionMembersProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.CoordGraph
import Elegant.Layered.Route
import Elegant.Layered.Labels
import Elegant.Layered.Compound
import Elegant.Layered.Order
import Elegant.Layered.Rank
import Elegant.Layered.ComponentCoverage

set_option autoImplicit false

open Elegant
open Elegant.Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact caption marker band (`XCA_MarkerBandBelowXW`)

Closes the marker-band residual of `ExactCaptionAncestorFactsProof.lean`
(`XCA_MarkerBandBelowX`): for an executed exact run, the rank band of an
ancestor group bottom marker lies below the caption band of a descendant
group. The tracked def has no local well-formedness premise; the scope
prefix step needs one, so this file states the W form
`XCA_MarkerBandBelowXW` and proves it, plus the W restatement of the
consumer (`XC_ancestorMarkerXW_holds`).

Chain: (a) nested bottom ranks over the exact ranking graph
(`excm_nested_bottom_rank`, replay of the private `lrr_nested_bottom_rank`
in `LoopResGroupHullRightAncestorRanksProof.lean` over
`Compound.rankingGraph` constraints via `ranked_compound_child_interval`);
(b) caption group top rank strictly below its own bottom marker
(`X_group_top_lt_bottom`); (c) reserved band tops are monotone in rank
(`X_ReserveBands_holds`, non-strict gap suffices) with the marker lower
bound from the same bands.

Probe: `proofs/wip/Probe/ExactCaptionAncestorFactsTProbe.lean`
(`bandViol=0` on flat, nested, fixed, wide, empty-nested, fixed-child, and
three-level inputs).
-/

/-- W form of `XCA_MarkerBandBelowX`: same statement with local admission
premises after the execution binder. -/
def XCA_MarkerBandBelowXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run →
    (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
    tNode.border = -2 →
    ∀ (pos : Nat) (fNode : Node),
    (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode →
    tNode.decl ≠ fNode.decl →
    tNode.clusterPath.contains fNode.decl = true →
    fNode.border = 2 →
    run.top.getD (rk run.coordinateProper.rank i).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank i).toNat []) ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).y
 /-- `excm_` copy of the private `X_take_is_prefix`
 (`ExactFlatC5Rank.lean`): a list take is a prefix. -/
 private theorem excm_take_is_prefix {α : Type} (l : List α) (n : Nat) :
     l.take n <+: l :=
   ⟨l.drop n, by simp⟩

 /-- `excm_` copy of the private `X_prefix_take_eq`
 (`ExactFlatC5Rank.lean`): a prefix is the take of its length. -/
 private theorem excm_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
     s.take p.length = p := by
   obtain ⟨r, rfl⟩ := hp
   simp

 /-- `excm_` copy of the private `X_prefix_of_common_prefix`
 (`ExactFlatC5Rank.lean`): of two prefixes of one list, the shorter prefixes
 the longer. -/
 private theorem excm_prefix_of_common_prefix {α : Type} {p q s : List α}
     (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
   obtain ⟨r₁, rfl⟩ := hp
   obtain ⟨r₂, hr⟩ := hq
   have h1 : (p ++ r₁).take p.length = p := excm_prefix_take_eq ⟨r₁, rfl⟩
   have h2 : (q ++ r₂).take p.length = q.take p.length := by
     have hz : p.length - q.length = 0 := by omega
     simp [List.take_append, hz]
   rw [← hr] at h1
   rw [h2] at h1
   rw [← h1]
   exact excm_take_is_prefix q p.length

 /-- `excm_` copy of the private `X_prefix_antisymm`
 (`ExactFlatC5Rank.lean`): mutual prefixes are equal. -/
 private theorem excm_prefix_antisymm {α : Type} {p q : List α}
     (h1 : p <+: q) (h2 : q <+: p) : p = q := by
   have e : q.take p.length = p := excm_prefix_take_eq h1
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

 /-- `excm_` copy of the private `X_prefix_length_lt`
 (`ExactFlatC5Rank.lean`): a strict prefix is strictly shorter. -/
 private theorem excm_prefix_length_lt {α : Type} {p s : List α}
     (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
   rcases Nat.lt_or_ge p.length s.length with h | h
   · exact h
   · have h2 : s <+: p :=
       excm_prefix_of_common_prefix ⟨[], by simp⟩ hp h
     exact absurd (excm_prefix_antisymm hp h2) hne

 /-- `excm_` copy of the private `X_dropLast_is_prefix`
 (`ExactFlatC5Rank.lean`): dropping the last element is a prefix. -/
 private theorem excm_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
   induction l with
   | nil => exact ⟨[], rfl⟩
   | cons a as ih =>
     cases as with
     | nil => exact ⟨[a], rfl⟩
     | cons b bs =>
       obtain ⟨r, hr⟩ := ih
       exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

 /-- `excm_` copy of the private `X_cg_path_last`
 (`ExactFlatC5Rank.lean`): a cluster path ending in `d` has last element `d`. -/
 private theorem excm_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
     {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
     p.getLast? = some d := by
   rw [h]
   simp
 /-- `excm_` copy of the private `X_titled_rank_prefix`
 (`ExactFlatC5Rank.lean`): title reservations extend the source rank. -/
 private theorem excm_titled_rank_prefix (P : Params) (exact : List Nat)
     (source : Proper) :
     ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
       source.rank ++ extra := by
   unfold titleReservations sizeProperPortsX
   exact ⟨_, rfl⟩

 /-- `excm_` copy of the private `X_titled_rank_record`
 (`ExactFlatC5Rank.lean`): source rank records survive title reservations. -/
 private theorem excm_titled_rank_record {P : Params} {exact : List Nat}
     {source : Proper} {index : Nat} {rank : Int}
     (h : source.rank[index]? = some rank) :
     (titleReservations (sizeProperPortsX P exact source)).rank[index]? =
       some rank := by
   obtain ⟨extra, heq⟩ := excm_titled_rank_prefix P exact source
   rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
   exact h

 /-- `excm_` copy of the private `X_coordinateGraph_rank_record`
 (`ExactFlatC5Rank.lean`): titled rank records survive cluster borders. -/
 private theorem excm_coordinateGraph_rank_record {P : Params} {exact : List Nat}
     {source : Proper} {index : Nat} {rank : Int}
     (h : (titleReservations (sizeProperPortsX P exact source)).rank[index]? =
       some rank) :
     (coordinateGraphX P exact source).rank[index]? = some rank := by
   obtain ⟨extra, heq⟩ := addClusterBorders_rank_prefix
     (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
   change (OrderImpl.addClusterBorders
     (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).rank[index]? =
       some rank
   rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
   exact h

 /-- `excm_` copy of the private `X_prepared_coordinate_original_rk`
 (`ExactFlatC5Rank.lean`): the exact coordinate rank at an original index
 equals the ranking rank. -/
 private theorem excm_prepared_coordinate_original_rk {P : Params} {exact : List Nat}
     {cg : Graph} {rr : RankImpl.RankResult} {source : Proper}
     (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
     (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
       source.rank[key]? = some rank)
     {index : Nat} (hindex : index < cg.nodes.length) :
     rk (coordinateGraphX P exact source).rank index = rk rr.ranks index := by
   obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
     (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
   have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
   have hirank : index < rr.ranks.length := by omega
   have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
     List.getElem?_eq_getElem hirank
   have hcoordinateLookup := excm_coordinateGraph_rank_record (P := P) (exact := exact)
     (excm_titled_rank_record (hranks index rr.ranks[index] hrrLookup))
   simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup,
     Option.getD_some]
 /-- `excm_` replay of the private `lrr_nested_bottom_rank`
 (`LoopResGroupHullRightAncestorRanksProof.lean`) over the exact ranking
 graph: for nested group tops, the inner bottom marker ranks at or below
 the outer bottom marker. -/
 private theorem excm_nested_bottom_rank {P : Params} {inp : Input} {o : Options}
     {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph}
     {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
     {rr : RankImpl.RankResult}
     (hrr : rankWithBudget (Compound.rankingGraph
       (componentCandidate graph comp candidate)) = .ok rr) :
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
   intro delta
   induction delta using Nat.strongRecOn with
   | _ delta ih =>
     intro a b na nb ba bb ha hbA hb hbB hpre hdelta hba hbb
     by_cases heq : na.clusterPath = nb.clusterPath
     · have hab : a = b := X_cg_top_unique h0 h hcomp ha hb hbA hbB heq
       subst hab
       have hdecl : na.decl = nb.decl := by
         have hlastA : na.clusterPath.getLast? = some na.decl := by
           obtain ⟨box, hbox, hpathA⟩ := X_cg_group_box h0 h ha hbA
           exact excm_cg_path_last hpathA
         have hlastB : nb.clusterPath.getLast? = some nb.decl := by
           obtain ⟨box, hbox, hpathB⟩ := X_cg_group_box h0 h hb hbB
           exact excm_cg_path_last hpathB
         have h := congrArg List.getLast? heq
         rw [hlastA, hlastB] at h
         exact Option.some.inj h
       rw [hdecl] at hba
       have hbb_eq : bb = ba := Option.some.inj (hbb.symm.trans hba)
       rw [hbb_eq]
       exact Int.le_refl _
     · have hlt : na.clusterPath.length < nb.clusterPath.length :=
         excm_prefix_length_lt hpre heq
       have hbne : nb.clusterPath ≠ [] :=
         (X_componentCandidate_marker_shape h0 h hb).2 hbB
       have hna_ne : na.clusterPath ≠ [] :=
         (X_componentCandidate_marker_shape h0 h ha).2 hbA
       obtain ⟨u, hu⟩ := X_candidate_parent_top_exists h0 h hlines hwf hframed
         hcomp candidate (x := (nb, b))
         (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpre hlt hna_ne
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
         excm_prefix_of_common_prefix hpre
           (huPath ▸ excm_dropLast_is_prefix nb.clusterPath) hleU
       have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
       obtain ⟨ubot, hubot⟩ :=
         X_componentRun_cg_bottom_find h0 h hlines hcomp huLookup huBorder
       obtain ⟨nbbot, hnbbot⟩ :=
         X_componentRun_cg_bottom_find h0 h hlines hcomp hb hbB
       have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
       have hIH := ih _ hdeltaU a u.2 na u.1 ba ubot ha hbA huLookup huBorder
         hpreU rfl hba hubot
       have hinterv := ranked_compound_child_interval (parent := (u.1, u.2))
         (child := (nb, b)) hrr
         (List.mem_zipIdx_iff_getElem?.mpr huLookup) huBorder hubot
         (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpathUB hnbbot
       have hbotStep : rk rr.ranks nbbot.2 + 1 ≤ rk rr.ranks ubot.2 := hinterv.2
       have hbbeq : bb = nbbot := Option.some.inj (hbb.symm.trans hnbbot)
       rw [hbbeq]
       omega




 /-- `excm_` replay of `bottomNestedBottomRankLe_wf`
 (`BottomNestedRankProof.lean`) over the exact run: the bottom marker of a
 group strictly inside another group ranks at or below the outer group
 bottom marker, in executed coordinate ranks. -/
 private theorem excm_nested_bottom_le {P : Params} {inp : Input} {o : Options}
     {exactIds : List String}
     {lines : List (List Measure.Line)} {graph0 graph : Graph}
     {measured : List MeasuredLabel}
     (h0 : measuredGraph P inp o lines = .ok graph0)
     (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hframed : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     {ex : List Nat}
     (hrun : componentRunX P ex (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v t : Nat} {ndV ndT : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
     (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
     (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
     (hdecl : ndV.decl = ndT.decl)
     {j : Nat} {nb : Node}
     (hjGet : (componentCandidate graph comp candidate).nodes[j]? = some nb)
     (hbordJ : nb.border = 2) (_hne : nb.decl ≠ ndT.decl)
     (hcontains : nb.clusterPath.contains ndT.decl = true) :
     rk run.coordinateProper.rank j ≤ rk run.coordinateProper.rank v := by
   obtain ⟨rr, labeled, hrr, hc, _, _, _, hranks, _⟩ :=
     X_cg_run_bundle h0 h hcomp hrun
   have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) =
       some (ndV, v) := by
     have hfindV := X_bottom_find_eq h0 h hcomp hvGet hbordV
     rw [← hdecl]
     exact hfindV
   obtain ⟨tn, htnFind⟩ :=
     X_componentRun_cg_top_of_bottom h0 h hlines hcomp hjGet hbordJ
   have htnPred := List.find?_some htnFind
   simp only [Bool.and_eq_true, beq_iff_eq] at htnPred
   obtain ⟨htnBorder, htnPathEq⟩ := htnPred
   have htnMem : tn ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
     List.mem_of_find?_eq_some htnFind
   have htnLookup : (componentCandidate graph comp candidate).nodes[tn.2]? =
       some tn.1 :=
     List.mem_zipIdx_iff_getElem?.mp htnMem
   have hdeclTn : tn.1.decl = nb.decl := by
     have hlastTn : tn.1.clusterPath.getLast? = some tn.1.decl := by
       obtain ⟨box, hbox, hpathTn⟩ := X_cg_group_box h0 h htnLookup htnBorder
       exact excm_cg_path_last hpathTn
     obtain ⟨boxM, hboxM, hpathM⟩ := X_cg_bottom_box h0 h hjGet hbordJ
     have hlastM : nb.clusterPath.getLast? = some nb.decl :=
       excm_cg_path_last hpathM
     have h := congrArg List.getLast? htnPathEq
     rw [hlastTn, hlastM] at h
     exact Option.some.inj h
   obtain ⟨tnBot, htnBot⟩ :=
     X_componentRun_cg_bottom_find h0 h hlines hcomp htnLookup htnBorder
   have hfindNb : (componentCandidate graph comp candidate).nodes.zipIdx.find?
       (fun entry => entry.1.border == 2 && entry.1.decl == nb.decl) =
       some (nb, j) :=
     X_bottom_find_eq h0 h hcomp hjGet hbordJ
   have htnBotEq : tnBot = (nb, j) := by
     rw [← hdeclTn] at hfindNb
     exact Option.some.inj (htnBot.symm.trans hfindNb)
   obtain ⟨boxT, hboxT, hpathT⟩ := X_cg_group_box h0 h htGet hbordT
   obtain ⟨boxM, hboxM, hpathM⟩ := X_cg_bottom_box h0 h hjGet hbordJ
   have hpreOuter : ndT.clusterPath <+: nb.clusterPath :=
     X_cg_scope_prefix hwf hboxT hpathT hboxM hpathM hcontains
   have hpre : ndT.clusterPath <+: tn.1.clusterPath := by
     rw [htnPathEq]
     exact hpreOuter
   have hrank := excm_nested_bottom_rank h0 h hlines hwf hframed hcomp candidate hrr
     _ t tn.2 ndT tn.1 (ndV, v) tnBot htGet hbordT htnLookup htnBorder hpre rfl
     hbotFindOuter htnBot
   have hjEq : tnBot.2 = j := congrArg Prod.snd htnBotEq
   rw [hjEq] at hrank
   have hvEq : ((ndV, v) : Node × Nat).2 = v := rfl
   rw [hvEq] at hrank
   have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
     have h1 := excm_prepared_coordinate_original_rk (P := P) (exact := ex) hrr
       hranks (List.getElem?_eq_some_iff.mp hvGet).1
     rw [hc] at h1
     exact h1
   have eJ : rk run.coordinateProper.rank j = rk rr.ranks j := by
     have h1 := excm_prepared_coordinate_original_rk (P := P) (exact := ex) hrr
       hranks (List.getElem?_eq_some_iff.mp hjGet).1
     rw [hc] at h1
     exact h1
   omega
 /-- `excm_` copy of the private `toNat_mono_of_nonneg`
 (`TimelineValidity.lean`): strict rank order survives `Int.toNat`. -/
 private theorem excm_toNat_mono_of_nonneg {a b : Int} (ha : 0 ≤ a) (h : a < b) :
     a.toNat < b.toNat := by
   have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
   have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha (Int.le_of_lt h))
   have h3 : (a.toNat : Int) < (b.toNat : Int) := by omega
   exact Int.ofNat_lt.mp h3
 /-- Exact marker band, W form: the rank band of an ancestor group bottom
 marker lies below the caption band of a descendant group over one executed
 exact run. Chain: nested bottom ranks
 (`excm_nested_bottom_le`), top strictly below own bottom
 (`X_group_top_lt_bottom`), reserved band monotonicity (`X_ReserveBands_holds`)
 plus the marker lower band bound. -/
 theorem excm_markerBandBelowXW_holds (exactIds : List String) :
     XCA_MarkerBandBelowXW exactIds := by
   intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
   intro i _stored0 tNode _hmem hnode hborder pos fNode hfn hne hcontain hbor2
   have hlines : execution.lines.length = inp.boxes.length := by
     have h := (mapM_getElem? _ _ _ execution.lines_eq).1
     simpa only [List.length_zipIdx] using h
   have hiLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnode).1
   have hposLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hfn).1
   obtain ⟨rr, _, hrr, hc, _, _, hranks, hlt⟩ :=
     X_group_top_lt_bottom execution.graph0_eq execution.graph_eq hcomp hrun
   obtain ⟨bottom, hfindB⟩ := X_componentRun_cg_bottom_find
     execution.graph0_eq execution.graph_eq hlines hcomp hnode hborder
   have hbotPred := List.find?_some hfindB
   simp only [Bool.and_eq_true, beq_iff_eq] at hbotPred
   obtain ⟨hbordB, hdeclB⟩ := hbotPred
   have hbotLookup : (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
       some bottom.1 :=
     List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfindB)
   have hbotLt : bottom.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hbotLookup).1
   have hltIR : rk rr.ranks i + 1 ≤ rk rr.ranks bottom.2 :=
     hlt i tNode bottom hnode hborder hfindB
   obtain ⟨ut, hutFind⟩ := X_componentRun_cg_top_of_bottom
     execution.graph0_eq execution.graph_eq hlines hcomp hfn hbor2
   have hutPred := List.find?_some hutFind
   simp only [Bool.and_eq_true, beq_iff_eq] at hutPred
   obtain ⟨huBorder, huPathEq⟩ := hutPred
   have huMem : ut ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
     List.mem_of_find?_eq_some hutFind
   have huLookup : (componentCandidate execution.graph comp candidate).nodes[ut.2]? =
       some ut.1 := List.mem_zipIdx_iff_getElem?.mp huMem
   have huLt : ut.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp huLookup).1
   have hdeclU : ut.1.decl = fNode.decl := by
     have hlastU : ut.1.clusterPath.getLast? = some ut.1.decl := by
       obtain ⟨box, hbox, hpathU⟩ := X_cg_group_box execution.graph0_eq
         execution.graph_eq huLookup huBorder
       exact excm_cg_path_last hpathU
     obtain ⟨boxM, hboxM, hpathM⟩ := X_cg_bottom_box execution.graph0_eq
       execution.graph_eq hfn hbor2
     have hlastM : fNode.clusterPath.getLast? = some fNode.decl :=
       excm_cg_path_last hpathM
     have h := congrArg List.getLast? huPathEq
     rw [hlastU, hlastM] at h
     exact Option.some.inj h
   have hpathBot : bottom.1.clusterPath = tNode.clusterPath := by
     obtain ⟨boxT, hboxT, hpathT⟩ := X_cg_group_box execution.graph0_eq
       execution.graph_eq hnode hborder
     obtain ⟨boxB, hboxB, hpathB⟩ := X_cg_bottom_box execution.graph0_eq
       execution.graph_eq hbotLookup hbordB
     have hboxEq : boxB = boxT := by
       have e1 : inp.boxes[bottom.1.decl]? = some boxB := hboxB
       have e2 : inp.boxes[tNode.decl]? = some boxT := hboxT
       rw [hdeclB] at e1
       exact Option.some.inj (e1.symm.trans e2)
     rw [hpathB, hpathT, hboxEq, hdeclB]
   have hneBU : bottom.1.decl ≠ ut.1.decl := by
     intro heq
     exact hne (hdeclB.symm.trans (heq.trans hdeclU))
   have hbotLe := excm_nested_bottom_le execution.graph0_eq execution.graph_eq
     hlines hwf hfp hcomp hrun hfn huLookup hbor2 huBorder hdeclU.symm
     hbotLookup hbordB hneBU (by rw [hpathBot, hdeclU]; exact hcontain)
   have eRi : rk run.coordinateProper.rank i = rk rr.ranks i := by
     have h1 := excm_prepared_coordinate_original_rk (P := execution.params)
       (exact := exactDecls exactIds inp) hrr hranks hiLt
     rw [hc] at h1
     exact h1
   have eRb : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
     have h1 := excm_prepared_coordinate_original_rk (P := execution.params)
       (exact := exactDecls exactIds inp) hrr hranks hbotLt
     rw [hc] at h1
     exact h1
   have eRp : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
     have h1 := excm_prepared_coordinate_original_rk (P := execution.params)
       (exact := exactDecls exactIds inp) hrr hranks hposLt
     rw [hc] at h1
     exact h1
   have hrankLe : rk run.coordinateProper.rank i + 1 ≤
       rk run.coordinateProper.rank pos := by
     rw [← eRi, ← eRb] at hltIR
     exact Int.le_trans hltIR hbotLe
   have hnnI : 0 ≤ rk run.coordinateProper.rank i := by
     rw [eRi]
     exact rankWithBudget_rk_nonneg hrr i
   have hnnP : 0 ≤ rk run.coordinateProper.rank pos := by
     rw [eRp]
     exact rankWithBudget_rk_nonneg hrr pos
   have hltNat : (rk run.coordinateProper.rank i).toNat <
       (rk run.coordinateProper.rank pos).toNat :=
     excm_toNat_mono_of_nonneg hnnI (by omega)
   obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, hroute, _, _⟩ :=
     componentRunX_spec hrun
   have hrouteOk := (RouteImpl.routeWithLanes_geometry hroute).1
   have hcov := (RouteImpl.layersOk_spec hrouteOk).2.2.2.1
   have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
   have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
     rw [hnodes]
     exact (proxyWidths_rel hprox).2.2.1
   have hiProper : i < run.proper.nodes.length :=
     componentRunX_original_nodes_covered hrun i hiLt
   have hposProper : pos < run.proper.nodes.length :=
     componentRunX_original_nodes_covered hrun pos hposLt
   obtain ⟨lI, hlyI, _, _⟩ := hcov i hiProper
   obtain ⟨lP, hlyP, hposMem, _⟩ := hcov pos hposProper
   rw [X_proper_rank_eq_local hrun i] at hlyI
   rw [X_proper_rank_eq_local hrun pos] at hlyP
   obtain ⟨hInBand, hDisj⟩ := X_ReserveBands_holds exactIds hrun
   have hposCoord : pos < run.coordinateProper.nodes.length := by
     rw [← hnodesLen]
     exact hposProper
   have hrankP : rk run.coordinateProper.rank pos =
       ((rk run.coordinateProper.rank pos).toNat : Int) :=
     (Int.toNat_of_nonneg hnnP).symm
   have hgetI : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = lI := by
     rw [List.getD_eq_getElem?_getD, hlyI]
     rfl
   rw [hgetI]
   refine Int.le_trans (hDisj _ _ _ _ hltNat hlyI hlyP) ?_
   have hframeY : (frameRect execution.params
       (componentCandidate execution.graph comp candidate) run pos).y =
       run.ys.getD pos 0 := by
     have hget : (componentCandidate execution.graph comp candidate).nodes.getD pos
         default = fNode := by
       simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
     simp only [frameRect, hget, hbor2,
       show ((2 : Int) != -2) = true from rfl, ↓reduceIte]
     rfl
   exact Int.le_trans ((hInBand _ _ _ hlyP hposMem hposCoord hrankP).1) (by omega)

/-- W form of `XCA_MarkerBelowX`: same statement with local admission
premises after the execution binder. -/
def XCA_MarkerBelowXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run →
    (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
    tNode.border = -2 →
    ∀ (pos : Nat) (fNode : Node),
    (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode →
    tNode.decl ≠ fNode.decl →
    tNode.clusterPath.contains fNode.decl = true →
    fNode.border = 2 →
    (transportCaption execution.params o execution.lines comp i stored0).y +
      (transportCaption execution.params o execution.lines comp i stored0).h ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).y

/-- Marker-below residual over the W band fact: replays
`XCA_markerBelowX_holds` (`ExactCaptionAncestorFactsProof.lean`) with the W
band hypothesis carrying the local admission premises. -/
theorem XCA_markerBelowXW_holds (exactIds : List String)
    (hcap : XC_CapBandX exactIds)
    (hmark : XCA_MarkerBandBelowXW exactIds) :
    XCA_MarkerBelowXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2
  exact Int.le_trans (hcap execution hcomp hrun i stored0 tNode hmem hnode hborder)
    (hmark execution hwf hfp hcomp hrun i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2)

/-- W restatement of the consumer: `XC_ancestorMarkerXW_holds`
(`ExactCaptionAncestorsLocalProof.lean:555`) replayed with the W marker-below
residual so the local admission premises reach the band proof. -/
theorem XC_ancestorMarkerXWW_holds (exactIds : List String)
    (hbelow : XCA_MarkerBelowXW exactIds) :
    XC_AncestorMarkerXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hancrel hbor2 hframe
  have hle := hbelow execution hwf hfp hcomp hrun i stored0 tNode hmem hnode hborder pos fNode hfn hne hancrel hbor2
  rw [hframe] at hle
  unfold Disjoint
  intro hcon
  obtain ⟨_, hy⟩ := hcon
  omega

end PipelineImpl

end Layered
end Elegant
