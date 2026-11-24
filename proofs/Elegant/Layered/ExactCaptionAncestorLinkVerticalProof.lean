import Elegant.Layered.ExactCaptionAncestorLinksProof
import Elegant.Layered.ExactCaptionMemberFactsProof
import Elegant.Layered.ExactFlatC5Bottom
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Coords
import Elegant.Layered.RouteTransport
import Elegant.Layered.Labels
import Elegant.Layered.Order
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameClearanceBottomFacts
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.CgShape

set_option autoImplicit false

open Elegant
open Elegant.Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact group-link vertical sides (`XCA_LinkTopXW`, `XCA_LinkBotXW`)

Closes the two vertical sides of the exact group link in W form
(`ExactCaptionAncestorLinksProof.lean`): a direct child group frame starts
strictly below its parent group frame top and ends strictly above its parent
frame bottom, over one executed exact run. The horizontal sides are already
proved (`XCA_LinkLeftXW_holds`, `XCA_LinkRightXW_holds`); this file assembles
`XCA_groupLinkXW_closed` with no premise.

Route: compound ranking gives parent top rank `<` child top rank and child
bottom rank `<` parent bottom rank through the nesting edges
(`ranked_compound_child_interval`); rank band tops are strictly monotone after
reservation (reserve-shift preservation below); member bounds transport the
band separation to the frame hulls. The top member bound replays through the
public `XC_childTopXW_holds`; the bottom member bound is classified below
(`xcv_memberRankLe`, replay of `Xb_memberRankLe`). Private helpers carry the
`xcv_` prefix.

Probe: `proofs/wip/Probe/ExactCaptionAncestorFactsTProbe.lean` checks all four
sides on flat, nested, fixed, wide, empty-nested, and fixed-child inputs with
zero violations.

Residual: `XCA_MarkerBandBelowX` (`ExactCaptionAncestorFactsProof.lean`)
remains open.
-/

private theorem xcv_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem xcv_le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

private theorem xcv_filter_ne_nil {α : Type} {l : List α}
    (h : l.isEmpty = false) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

private theorem xcv_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

private theorem xcv_toNat_le_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.toNat ≤ b.toNat) : a ≤ b := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by exact_mod_cast h
  omega

private theorem xcv_rkToNat_le {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) :
    a.toNat ≤ b.toNat := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha h)
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by omega
  exact Int.ofNat_le.mp h3

private theorem xcv_pairwise_getD_le {l : List Int} (hp : l.Pairwise (· ≤ ·))
    {i j : Nat} (hij : i < j) (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := by omega
  have hgi : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  have hgj : l[j]? = some l[j] := List.getElem?_eq_getElem hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hgi, hgj]
  simp only [Option.getD_some]
  exact hp.rel_getElem_of_lt hi hj hij

private theorem xcv_prefix_length (es : List Int) (s : Int) (out : List Int) :
    ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2).length =
      out.length + es.length := by
  induction es generalizing s out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega


private theorem xcv_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

private theorem xcv_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := xcv_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

private theorem xcv_titled_copy_rank_record {P : Params} {exact : List Nat} {labeled : Proper}
    (haligned : labeled.nodes.length = labeled.rank.length)
    {position : Nat} {entry : ProperNode × Nat}
    (hentry : (titleNodes (sizeProperPortsX P exact labeled))[position]? = some entry) :
    (titleReservations (sizeProperPortsX P exact labeled)).rank[labeled.nodes.length + position]? =
      some (rk labeled.rank entry.2) := by
  have hsized : (sizeProperPortsX P exact labeled).rank = labeled.rank := rfl
  have hrank : (titleReservations (sizeProperPortsX P exact labeled)).rank =
      labeled.rank ++ (titleNodes (sizeProperPortsX P exact labeled)).map
        (fun value => rk labeled.rank value.2) := by
    have h0 : (titleReservations (sizeProperPortsX P exact labeled)).rank =
        (sizeProperPortsX P exact labeled).rank ++
          (titleNodes (sizeProperPortsX P exact labeled)).map
            (fun value => rk (sizeProperPortsX P exact labeled).rank value.2) := by
      unfold titleReservations titleNodes sizeProperPortsX
      rfl
    rw [h0, hsized]
  rw [hrank, List.getElem?_append_right (by omega)]
  have hindex : labeled.nodes.length + position - labeled.rank.length = position := by omega
  rw [hindex, List.getElem?_map, hentry]
  rfl

private theorem xcv_coord_titled_rank_record {P : Params} {exact : List Nat} {labeled : Proper}
    {index : Nat} {rank : Int}
    (h : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? = some rank) :
    (coordinateGraphX P exact labeled).rank[index]? = some rank := by
  obtain ⟨extraC, heqC⟩ := coordinateGraphX_anchor_prefix P exact labeled
  obtain ⟨extraA, heqA⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hlen : index < (titleReservations (sizeProperPortsX P exact labeled)).rank.length :=
    (List.getElem?_eq_some_iff.mp h).1
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank[index]? =
      some rank := by
    have hrfl : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank =
        (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank := rfl
    rw [hrfl, heqA, List.getElem?_append_left (by omega : index < (titleReservations
      (sizeProperPortsX P exact labeled)).rank.length)]
    exact h
  have hmat : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank[index]? =
      some rank := by
    have hrfl : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW))).rank =
        (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).rank := rfl
    rw [hrfl]; exact hclear
  have hunfold : coordinateGraphX P exact labeled =
      materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)) := rfl
  rw [hunfold]; exact hmat
private theorem xcv_coord0_lookup (P : Params) (exact : List Nat)
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

private theorem xcv_coord_lookup (P : Params) (exact : List Nat)
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
  rcases xcv_coord0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3
private theorem xcv_nonproxy {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]
private theorem xcv_title_rank_source {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper}
    (hkeys : NodeKeys cg labeled) (hshape : CgShape cg)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {titleIndex : Nat} {title : ProperNode}
    (htitle : (coordinateGraphX P exact labeled).nodes[titleIndex]? = some title)
    (hborder : title.node.border = 3) :
    ∃ (originalIndex : Nat) (original : ProperNode),
      labeled.nodes[originalIndex]? = some original ∧
      original.node.border = -2 ∧ original.dummy = false ∧
      title.dummy = false ∧ title.node.clusterPath = original.node.clusterPath ∧
      rk (coordinateGraphX P exact labeled).rank titleIndex = rk labeled.rank originalIndex := by
  rcases xcv_coord_lookup P exact labeled htitle with
    ⟨original, horiginal, _, hb, _, _⟩ | ⟨_, hside⟩ |
    ⟨position, entry, hentry, hindex, hd, _, hp⟩
  · rcases hkeys titleIndex original horiginal with
      ⟨before, hbefore, _, hbeforeBorder, _⟩ | ⟨_, hplain, _⟩
    · have hnot := hshape.2 before (List.mem_of_getElem? hbefore)
      exact (hnot (hbeforeBorder.symm.trans (hb.symm.trans hborder))).elim
    · omega
  · rcases hside with hside | hside <;> omega
  · obtain ⟨hsized, hsizedBorder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hsourceDummy, hsourceBorder, hsourcePath⟩ :=
      X_sizeProperPorts_node_origin P exact labeled hsized
    have hsourceGroup : original.node.border = -2 := hsourceBorder.symm.trans hsizedBorder
    have horiginalReal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · omega
    have hentryReal : entry.1.dummy = false := hsourceDummy.trans horiginalReal
    have htitleReal : title.dummy = false := hd.trans hentryReal
    have htitlePath : title.node.clusterPath = original.node.clusterPath :=
      (hp hentryReal).trans hsourcePath
    have htitledRank := xcv_titled_copy_rank_record haligned hentry
    have hcoordinateRank := xcv_coord_titled_rank_record htitledRank
    refine ⟨entry.2, original, horiginal, hsourceGroup, horiginalReal,
      htitleReal, htitlePath, ?_⟩
    rw [hindex]
    simp only [rk, List.getD_eq_getElem?_getD, hcoordinateRank, Option.getD_some]

private theorem xcv_coord_rank_eq {P : Params} {exact : List Nat} {labeled : Proper} {run : Run}
    (hcoord : coordinateGraphX P exact labeled = run.coordinateProper)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {x : Nat} (hx : x < labeled.nodes.length) :
    rk run.coordinateProper.rank x = rk labeled.rank x := by
  have hxr : x < labeled.rank.length := by omega
  have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
    List.getElem?_eq_getElem hxr
  obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
  have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
    rw [← hcoord, heq, List.getElem?_append_left hxr]
    exact hlab
  simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

private theorem xcv_titled_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact labeled)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  obtain ⟨_, heq⟩ := xcv_titled_rank_prefix P exact labeled
  have htitledLookup : (titleReservations (sizeProperPortsX P exact labeled)).rank[index]? =
      some rr.ranks[index] := by
    rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hlabLookup).1]
    exact hlabLookup
  have heq2 : rk (titleReservations (sizeProperPortsX P exact labeled)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq2, ?_⟩
  rw [heq2]
  exact rankWithBudget_rk_nonneg hrr index

private theorem xcv_prepared_rk {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {rr : RankImpl.RankResult} {labeled : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      labeled.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk run.coordinateProper.rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hlabLookup := hranks index rr.ranks[index] hrrLookup
  have hlabLen : index < labeled.rank.length :=
    (List.getElem?_eq_some_iff.mp hlabLookup).1
  obtain ⟨_, _, heq⟩ := coordinateGraphX_anchor_prefix P exact labeled
  have hcoordLookup : run.coordinateProper.rank[index]? = some rr.ranks[index] := by
    rw [← hc, heq, List.getElem?_append_left hlabLen]
    exact hlabLookup
  simp only [rk, List.getD_eq_getElem?_getD, hcoordLookup, hrrLookup, Option.getD_some]

private theorem xcv_fbs {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', -, hb', hh'⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [← hdrop]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  refine ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm, ?_⟩
  intro hnp
  obtain ⟨hfull, -⟩ := xcv_nonproxy hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

private theorem xcv_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
      run.proper.nodes[index]? =
        some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf run.proper run.xs index = span.lo ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

private theorem xcv_run_pre {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (y_pre top_pre ys_pre : List Int),
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
      proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
      reserveExactRanks cg exact labels run.coordinateProper run.layers ys_pre top_pre =
        .ok (run.ys, run.top) ∧
      run.coordinateYs = y_pre := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := xcv_bind_ok h
  obtain ⟨p0, hp0, h⟩ := xcv_bind_ok h
  obtain ⟨q, hq, h⟩ := xcv_bind_ok h
  obtain ⟨ord, hord, h⟩ := xcv_bind_ok h
  obtain ⟨xs, hxs, h⟩ := xcv_bind_ok h
  obtain ⟨routed, hprojection, h⟩ := xcv_bind_ok h
  obtain ⟨lanes, hr, h⟩ := xcv_bind_ok h
  obtain ⟨yt, hy, h⟩ := xcv_bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := xcv_bind_ok h
  obtain ⟨routes, hroutes, h⟩ := xcv_bind_ok h
  have he := Except.ok.inj h
  subst he
  cases yt with
  | mk y top =>
    exact ⟨y, top, _, hy, rfl, hres, rfl⟩
private theorem xcv_foldl_preserves (step : List Int → (Node × Nat) → List Int)
    (topLen : Nat)
    (hstep : ∀ acc q, acc.length = topLen → (∀ i, 0 ≤ acc.getD i 0) →
      (step acc q).length = topLen ∧ ∀ i, 0 ≤ (step acc q).getD i 0)
    (xs : List (Node × Nat)) (acc : List Int)
    (hlen : acc.length = topLen) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (xs.foldl step acc).length = topLen ∧
      ∀ i, 0 ≤ (xs.foldl step acc).getD i 0 := by
  induction xs generalizing acc with
  | nil => exact ⟨hlen, hpos⟩
  | cons q xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hlen', hpos'⟩ := hstep acc q hlen hpos
    exact ih _ hlen' hpos'

private theorem xcv_extra_step_preserves (acc : List Int) (m : Nat) (needed : Int)
    (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (acc.set m (max (acc.getD m 0) needed)).length = acc.length ∧
      ∀ i, 0 ≤ (acc.set m (max (acc.getD m 0) needed)).getD i 0 := by
  refine ⟨List.length_set, ?_⟩
  intro i
  have hset : (acc.set m (max (acc.getD m 0) needed))[i]? =
      if m = i then if m < acc.length then some (max (acc.getD m 0) needed) else none
      else acc[i]? :=
    List.getElem?_set
  rw [List.getD_eq_getElem?_getD, hset]
  by_cases heq : m = i
  · subst heq
    by_cases hlt : m < acc.length
    · have h0 : 0 ≤ acc[m] := by
        have h := hpos m
        simpa [hlt] using h
      simp [hlt]
      exact Int.le_trans h0 (Int.le_max_left _ _)
    · simp [hlt]
  · have hne : m ≠ i := heq
    simp [hne]
    exact hpos i

private theorem xcv_extra_step_concrete (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int)
    (acc : List Int) (q : Node × Nat)
    (hlen : acc.length = top.length) (hpos : ∀ i, 0 ≤ acc.getD i 0) :
    (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
            Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) - top.getD ((p.rank.getD q.2 0).toNat) 0 -
            heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
              Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
              top.getD ((p.rank.getD q.2 0).toNat) 0 -
              heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
  by_cases h1 : (!exact.contains q.1.decl) = true
  · rw [ite_eq_left h1]
    exact ⟨hlen, hpos⟩
  · rw [ite_eq_right h1]
    by_cases h2 : (loopSizes cg.edges labels q.2 cg.slot).isEmpty = true
    · rw [ite_eq_left h2]
      exact ⟨hlen, hpos⟩
    · rw [ite_eq_right h2]
      obtain ⟨hlen', hpos'⟩ := xcv_extra_step_preserves acc _ _ hpos
      exact ⟨hlen'.trans hlen, hpos'⟩

private theorem xcv_extra_fold (cg : Graph) (exact : List Nat)
    (labels : List MeasuredLabel) (p : Proper) (ys top heights : List Int) :
    let extra := cg.nodes.zipIdx.foldl (fun (acc : List Int) (q : Node × Nat) =>
      if !exact.contains q.1.decl then acc
      else
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        if sizes.isEmpty then acc
        else
          let rank := (p.rank.getD q.2 0).toNat
          let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
          let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
            heights.getD rank 0
          acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length (0 : Int))
    extra.length = top.length ∧ ∀ i, 0 ≤ extra.getD i 0 := by
  have hbase : (List.replicate top.length (0 : Int)).length = top.length := by simp
  have hbasePos : ∀ i, 0 ≤ (List.replicate top.length (0 : Int)).getD i 0 := by
    intro i
    by_cases h : i < top.length
    · have hg : (List.replicate top.length (0 : Int))[i]? = some 0 := by
        rw [List.getElem?_eq_getElem (by simpa using h)]
        simp
      rw [List.getD_eq_getElem?_getD, hg]
      simp
    · have hg : (List.replicate top.length (0 : Int))[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by simpa using Nat.le_of_not_gt h)
      rw [List.getD_eq_getElem?_getD, hg]
      simp
  have hstep : ∀ (acc : List Int) (q : Node × Nat), acc.length = top.length →
    (∀ i, 0 ≤ acc.getD i 0) →
      (if !exact.contains q.1.decl then acc
      else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
      else acc.set ((p.rank.getD q.2 0).toNat)
        (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
          (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
            Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
            top.getD ((p.rank.getD q.2 0).toNat) 0 -
            heights.getD ((p.rank.getD q.2 0).toNat) 0))).length = top.length ∧
      ∀ i, 0 ≤ (if !exact.contains q.1.decl then acc
        else if (loopSizes cg.edges labels q.2 cg.slot).isEmpty then acc
        else acc.set ((p.rank.getD q.2 0).toNat)
          (max (acc.getD ((p.rank.getD q.2 0).toNat) 0)
            (ys.getD q.2 0 + max q.1.h ((loopSizes cg.edges labels q.2 cg.slot).length *
              Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot)) -
              top.getD ((p.rank.getD q.2 0).toNat) 0 -
              heights.getD ((p.rank.getD q.2 0).toNat) 0))).getD i 0 := by
    intro acc q hlen hpos
    exact xcv_extra_step_concrete cg exact labels p ys top heights acc q hlen hpos
  have h := xcv_foldl_preserves (fun (acc : List Int) (q : Node × Nat) =>
    if !exact.contains q.1.decl then acc
    else
      let sizes := loopSizes cg.edges labels q.2 cg.slot
      if sizes.isEmpty then acc
      else
        let rank := (p.rank.getD q.2 0).toNat
        let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
        let needed := ys.getD q.2 0 + reserved - top.getD rank 0 -
          heights.getD rank 0
        acc.set rank (max (acc.getD rank 0) needed)) top.length hstep
    cg.nodes.zipIdx (List.replicate top.length (0 : Int)) hbase hbasePos
  exact h

private theorem xcv_shift_strict_tops {p : Proper} {layers : List (List Nat)}
    {top : List Int} {extra shifts : List Int} {top' : List Int}
    (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top.getD r' 0)
    (hextraLen : extra.length = top.length)
    (hpos : ∀ e ∈ extra, 0 ≤ e)
    (hshifts : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)
    (htopLen : top.length = layers.length)
    (htop : ∀ (r : Nat), r < top.length → top'.getD r 0 = top.getD r 0 + shifts.getD r 0) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → layers[r]? = some l →
      layers[r']? = some l' →
      top'.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top'.getD r' 0 := by
  have hshiftsLen : shifts.length = top.length := by
    rw [hshifts, xcv_prefix_length]
    simp [hextraLen]
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hshifts]
    exact reserveShift_prefix_pairwise extra hpos 0 [] (by simp) (by simp)
  have hmono : ∀ i j, i < j → j < shifts.length →
      shifts.getD i 0 ≤ shifts.getD j 0 :=
    fun i j hij hj => xcv_pairwise_getD_le hpair hij hj
  intro r r' l l' hlt hly hly'
  have hrTop : r < top.length := by
    rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly).1
  have hrTop' : r' < top.length := by
    rw [htopLen]; exact (List.getElem?_eq_some_iff.mp hly').1
  have hrShift' : r' < shifts.length := by rw [hshiftsLen]; exact hrTop'
  have e1 := htop r hrTop
  have e1' := htop r' hrTop'
  have hle := hmono r r' hlt hrShift'
  have hd := hdisj r r' l l' hlt hly hly'
  rw [e1, e1']
  omega
private theorem xcv_shift_eqs {P : Params} {inp : Input} {exactIds : List String}
    {graph : Graph} {comp : List Nat}
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    ∃ (y_pre top_pre ys_pre : List Int),
      rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (y_pre, top_pre) ∧
      proxyYs run.coordinateProper run.layers top_pre y_pre = ys_pre ∧
      (∀ r, r < top_pre.length → run.top.getD r 0 = top_pre.getD r 0 +
        (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
                (componentCandidate graph comp candidate).slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                  (componentCandidate graph comp candidate).slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h
                    (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0) ∧
      (∀ j, j < ys_pre.length → run.ys.getD j 0 = ys_pre.getD j 0 +
        (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
                (componentCandidate graph comp candidate).slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                  (componentCandidate graph comp candidate).slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h
                    (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD
          ((run.coordinateProper.rank.getD j 0).toNat) 0) := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := xcv_run_pre hrun
  refine ⟨y_pre, top_pre, ys_pre, hry, hyspre, ?_, ?_⟩
  · unfold reserveExactRanks at hreserve
    obtain ⟨topNew, htopM, h1⟩ := xcv_bind_ok hreserve
    obtain ⟨ysNew, hysM, h2⟩ := xcv_bind_ok h1
    have hpair := Except.ok.inj h2
    have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
    rw [htopNew_eq] at htopM
    intro r hr
    have hrZ : r < (top_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hr
    have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
      have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
    obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
    have hbeq := Measure.checkedI32_ok hb
    have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
    have e3 : top_pre.getD r 0 = top_pre[r] := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    have e4 : run.top.getD r 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq
  · unfold reserveExactRanks at hreserve
    obtain ⟨topNew, htopM, h1⟩ := xcv_bind_ok hreserve
    obtain ⟨ysNew, hysM, h2⟩ := xcv_bind_ok h1
    have hpair := Except.ok.inj h2
    have hysNew_eq : ysNew = run.ys := congrArg Prod.fst hpair
    rw [hysNew_eq] at hysM
    intro j hj
    have hjZ : j < (ys_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hj
    have hzin : (ys_pre.zipIdx)[j]? = some (ys_pre[j], j) := by
      have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ hysM
    obtain ⟨b, hb, hbr⟩ := hidx j _ hzin
    have hbeq := Measure.checkedI32_ok hb
    have h1 : ys_pre[j]? = some ys_pre[j] := List.getElem?_eq_getElem hj
    have e3 : ys_pre.getD j 0 = ys_pre[j] := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    have e4 : run.ys.getD j 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq
private theorem xcv_post_gap {P : Params} {inp : Input} {exactIds : List String}
    {graph : Graph} {comp : List Nat} {candidate : Nat} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        run.top.getD r' 0 := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, htop, hys⟩ := xcv_shift_eqs hrun
  have hdisjPre : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      top_pre.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l + 1 ≤
        top_pre.getD r' 0 :=
    fun r r' l l' hlt hly hly' => rankAxis_band_top_strict hry r r' l l' hlt hly hly'
  have hextra := xcv_extra_fold (componentCandidate graph comp candidate)
    (exactDecls exactIds inp) labels run.coordinateProper
    ys_pre top_pre
    (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
  have hposM : ∀ e ∈ (componentCandidate graph comp candidate).nodes.zipIdx.foldl
      (fun (acc : List Int) (q : Node × Nat) =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
            (componentCandidate graph comp candidate).slot
          if sizes.isEmpty then acc
          else
            let rank := (run.coordinateProper.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band
              (componentCandidate graph comp candidate).slot sizes)
            let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
              (run.layers.map fun layer => layer.foldl (fun h v => max h
                (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed))
      (List.replicate top_pre.length (0 : Int)), 0 ≤ e := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    have h := hextra.2 i
    rw [List.getD_eq_getElem?_getD, hi] at h
    simp at h
    exact h
  have htopLen : top_pre.length = run.layers.length :=
    (CoordsImpl.rankCoordsWith_length hry).2
  exact xcv_shift_strict_tops hdisjPre hextra.1 hposM rfl htopLen htop
private theorem xcv_top_coord {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = -2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact)
    hrec (Or.inl hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inl hgroup))

private theorem xcv_top_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath := by
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    xcv_proxy_interval hrun hcoord (Or.inl hb)
  exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

private theorem xcv_bottom_coord {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact)
    hrec (Or.inr hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))

private theorem xcv_bottom_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    xcv_proxy_interval hrun hcoord (Or.inr hb)
  refine ⟨_, hproper, rfl, ?_⟩
  simp only [RouteImpl.nodeH, hproper]
  exact hcoordH
private theorem xcv_bottom_marker {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {t : Nat} {ndT : Node}
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordT : ndT.border = -2) :
    ∃ (v : Nat) (ndV : Node),
      (componentCandidate graph comp candidate).nodes[v]? = some ndV ∧
      ndV.border = 2 ∧ ndV.decl = ndT.decl := by
  obtain ⟨_, labeledB, bottom, _, _, hkB, _, hrecordsB, _, _, hfindB⟩ :=
    X_group_bottom_source h0 h hcomp hrun htGet hbordT
  obtain ⟨ndV, hvGet, hbordV, hpathV, _, _⟩ :=
    X_bottom_constraint_source h0 h hkB hrecordsB htGet hbordT hfindB
  obtain ⟨boxT, _, hpathT⟩ := X_cg_group_box h0 h htGet hbordT
  obtain ⟨boxV, _, hpathVbox⟩ := X_cg_bottom_box h0 h hvGet hbordV
  have hdecl : ndV.decl = ndT.decl := by
    have heq : Compound.path inp.boxes boxV ++ [ndV.decl] =
        Compound.path inp.boxes boxT ++ [ndT.decl] := by
      rw [← hpathVbox, hpathV, hpathT]
    have hlast := congrArg List.getLast? heq
    simp at hlast
    exact hlast
  exact ⟨_, _, hvGet, hbordV, hdecl⟩

private theorem xcv_bottom_frame_eq {P : Params} {cg : Graph} {run : Run}
    {gpos : Nat} {gn : Node}
    (hg : cg.nodes[gpos]? = some gn) (hgroup : gn.border = -2) :
    (frameRect P cg run gpos).y + (frameRect P cg run gpos).h =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom := by
  have hgroupGet : cg.nodes.getD gpos default = gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  simp only [frameRect, hgroupGet, hgroup,
    show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  change (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
    if q.1.node.clusterPath.contains gn.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none) []).minY +
    ((boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains gn.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none) []).bottom - (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains gn.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none) []).minY) = _
  omega

private theorem xcv_rect_mem_frame_hull {cg : Graph} {run : Run} {gpos v : Nat}
    {pn : ProperNode}
    (hv : run.proper.nodes[v]? = some pn)
    (hpath : (cg.nodes.getD gpos default).decl ∈ pn.node.clusterPath) :
    Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD gpos default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  have hmem : (pn, v) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hv
  have hcond : (pn, v).fst.node.clusterPath.contains
      (cg.nodes.getD gpos default).decl = true :=
    List.contains_iff_mem.mpr hpath
  apply List.mem_filterMap.mpr
  refine ⟨(pn, v), hmem, ?_⟩
  rw [hcond]
  simp

private theorem xcv_bottom_hull_mem {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate graph comp candidate).nodes[gpos]? = some gn)
    (_hgroup : gn.border = -2)
    {v : Nat} {ndV : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (hbordV : ndV.border = 2) (hdecl : ndV.decl = gn.decl) :
    Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  obtain ⟨bcoord, hbcoord, hbb, _, hpathB, hcoordH⟩ :=
    xcv_bottom_coord h0 h hcomp hrun hvGet hbordV
  obtain ⟨bprop, hbprop, hpathProp, _⟩ :=
    xcv_bottom_proper hrun hbcoord hbb hcoordH
  obtain ⟨_, _, hpathVbox⟩ := X_cg_bottom_box h0 h hvGet hbordV
  have hbcontains : bprop.node.clusterPath.contains gn.decl = true := by
    rw [hpathProp, hpathB, hpathVbox, hdecl]; simp
  have hgroupGet : (componentCandidate graph comp candidate).nodes.getD gpos default =
      gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  have hpath' : ((componentCandidate graph comp candidate).nodes.getD gpos default).decl ∈
      bprop.node.clusterPath := by
    rw [hgroupGet]; exact List.contains_iff_mem.mp hbcontains
  rw [← hgroupGet]
  exact xcv_rect_mem_frame_hull hbprop hpath'
private theorem xcv_revKey {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactFramePrefix exactIds inp o)
    {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
    ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
      nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
  have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  have hvlt : v < execution.graph0.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    omega
  have hmem : execution.graph0.nodes[v]? = some execution.graph0.nodes[v] :=
    List.getElem?_eq_getElem hvlt
  obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key execution.graph_eq hmem
  have heq : nd'' = nd := Option.some.inj (hnd''.symm.trans h)
  subst heq
  exact ⟨_, hmem, hd.symm, hb.symm, hc.symm⟩

private theorem xcv_groupPath {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactFramePrefix exactIds inp o)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box ++ [index] := by
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnode hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, hdecl, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap, hdecl] at hpath
  exact hpath

private theorem xcv_direct_group_path {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    child.clusterPath.dropLast = parent.clusterPath := by
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := xcv_revKey execution hparentSource
  obtain ⟨_, _, hchildSource⟩ := componentCandidate_nonplain_source hchild (by omega)
  obtain ⟨child0, hchild0, hdC, hbC, hpC⟩ := xcv_revKey execution hchildSource
  obtain ⟨parentOriginal, hparentOriginal, hparentDecl, hparentPath⟩ :=
    xcv_groupPath execution hparent0 (hbP.trans hparentGroup)
  obtain ⟨childOriginal, hchildOriginal, hchildDecl, hchildPath⟩ :=
    xcv_groupPath execution hchild0 (hbC.trans hchildGroup)
  have hparentEq : parentOriginal = parentBox := by
    rw [← hparentDecl, hdP] at hparentOriginal
    exact Option.some.inj (hparentOriginal.symm.trans hparentBox)
  have hchildEq : childOriginal = childBox := by
    rw [← hchildDecl, hdC] at hchildOriginal
    exact Option.some.inj (hchildOriginal.symm.trans hchildBox)
  have himmediate := Compound.path_of_parent (inputModel inp o) hwf
    hparentBox hchildBox hparentRef hne
  have hparentPathEq : parent.clusterPath = Compound.path inp.boxes parentBox ++ [parent.decl] := by
    rw [← hpP, hparentPath, ← hparentDecl, hdP, hparentEq]
  have hchildPathEq : child.clusterPath = Compound.path inp.boxes childBox ++ [child.decl] := by
    rw [← hpC, hchildPath, ← hchildDecl, hdC, hchildEq]
  calc
    child.clusterPath.dropLast = Compound.path inp.boxes childBox := by
      rw [hchildPathEq, List.dropLast_concat]
    _ = Compound.path inp.boxes parentBox ++ [parent.decl] := himmediate
    _ = parent.clusterPath := hparentPathEq.symm

private theorem xcv_foldl_strict_minY (rects : List Rect) (b : Bounds) (lo : Int)
    (hb : lo < b.minY) (hall : ∀ r ∈ rects, lo < r.y) :
    lo < ((rects.foldl fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY := by
  induction rects generalizing b with
  | nil => simpa using hb
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · show lo < min b.minY first.y
      have h1 := hb
      have h2 := hall first (by simp)
      omega
    · intro r hr
      exact hall r (List.mem_cons_of_mem _ hr)

private theorem xcv_strict_minY (rects : List Rect) (lo : Int)
    (hall : ∀ r ∈ rects, lo < r.y) (hne : rects ≠ []) :
    lo < (boundsOf rects []).minY := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    unfold boundsOf
    exact xcv_foldl_strict_minY _ _ _ (hall first (by simp)) hall

private theorem xcv_origRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds) :
    ∀ {idx : Nat} {n : Node},
    (componentCandidate graph comp candidate).nodes[idx]? = some n →
    n.clusterPath.contains ndT.decl = true →
    rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v := by

  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hfindV : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndV.decl) = some (ndV, v) :=
    X_bottom_find_eq h0 h hcomp hvGet hbordV
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) = some (ndV, v) := by
    rw [← hdecl]; exact hfindV
  have htopOuter : ((ndT, t) : Node × Nat) ∈
      (componentCandidate graph comp candidate).nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htGet
  have eV : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := xcv_prepared_rk hrr hc hranks (List.getElem?_eq_some_iff.mp hvGet).1
    exact h1
  let cg := componentCandidate graph comp candidate
  let maxLen := ((cg.nodes.filter fun n => n.border == -2).map
    (fun n => n.clusterPath.length)).foldr max 0

  have hbound : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath.length ≤ maxLen := by
    intro index node hnode hgroup
    have hmem : node ∈ cg.nodes.filter (fun n => n.border == -2) :=
      List.mem_filter.mpr ⟨List.mem_of_getElem? hnode, by simp [hgroup]⟩
    have hmap : node.clusterPath.length ∈
        (cg.nodes.filter fun n => n.border == -2).map
          (fun n => n.clusterPath.length) :=
      List.mem_map_of_mem hmem
    exact xcv_le_foldr_max hmap
  have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath ≠ [] := by
    intro index node hnode hgroup hnil
    exact (X_componentCandidate_marker_shape h0 h hnode).2 hgroup hnil
  have main : ∀ fuel idx n, cg.nodes[idx]? = some n →
      n.clusterPath.contains ndT.decl = true →
      maxLen - n.clusterPath.length = fuel → rk rr.ranks idx ≤ rk rr.ranks v := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro idx n hidx hcontains hfuel
      rcases (X_componentCandidate_marker_shape h0 h hidx).1 with hplain | hgroup | hbottom
      · have hinterval := ranked_compound_member_interval hrr htopOuter hbordT
          hbotFindOuter (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hplain hcontains
        have hle : rk rr.ranks idx + 1 ≤ rk rr.ranks v := hinterval.2
        omega
      · obtain ⟨rrB, labeledB, bottomTB, hrrB, hcB, hkB, hreadyB, hrecordsB, hranksB,
            htitledB, hfindB⟩ :=
          X_group_bottom_source h0 h hcomp hrun hidx hgroup
        obtain ⟨origB, horigB, hborderB, hpathB, hrecordB, hfindCB⟩ :=
          X_bottom_constraint_source h0 h hkB hrecordsB hidx hgroup hfindB
        have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
          rw [hpathB]; exact hcontains
        have resolveB : rk rr.ranks bottomTB.2 ≤ rk rr.ranks v := by
          by_cases hdeq : origB.decl = ndT.decl
          · have hmemB := List.find?_some hfindCB
            simp only [Bool.and_eq_true, beq_iff_eq] at hmemB
            have hndeq : n.decl = ndT.decl := hmemB.2.symm.trans hdeq
            rw [hndeq] at hfindCB
            have heq : (origB, bottomTB.2) = (ndV, v) :=
              Option.some.inj (hfindCB.symm.trans hbotFindOuter)
            have hbv : bottomTB.2 = v := congrArg Prod.snd heq
            rw [hbv]
            exact Int.le_refl _
          · have hleB : rk run.coordinateProper.rank bottomTB.2 ≤
                rk run.coordinateProper.rank v :=
              hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
                horigB hborderB hdeq hpathBmem
            have e1 : rk run.coordinateProper.rank bottomTB.2 =
                rk rr.ranks bottomTB.2 := by
              have h1 := xcv_prepared_rk hrr hc hranks
                (List.getElem?_eq_some_iff.mp horigB).1
              exact h1
            omega
        cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
            entry.1.border == 0 && entry.1.clusterPath.contains n.decl).isEmpty with
        | false =>
          obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
            (xcv_filter_ne_nil hmemCase)
          obtain ⟨hmemberZip, hmemberCond⟩ := List.mem_filter.mp hmember
          obtain ⟨hmemberPlain, hmemberInside⟩ := Bool.and_eq_true_iff.mp hmemberCond
          have hmemberPlain' : member.1.border = 0 := by simpa using hmemberPlain
          have hmemberInside' : member.1.clusterPath.contains n.decl = true := by
            simpa using hmemberInside
          have hinterval := ranked_compound_member_interval hrr
            (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
            hmemberZip hmemberPlain' hmemberInside'
          have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks member.2 := hinterval.1
          have hR : rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottomTB.2 := hinterval.2
          omega
        | true =>
          cases hchildCase : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
              fun entry => entry.1.clusterPath.dropLast == n.clusterPath).isEmpty with
          | false =>
            obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _
              (xcv_filter_ne_nil hchildCase)
            obtain ⟨hchildTop, hchildPathEq⟩ := List.mem_filter.mp hchildMem
            obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
            have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
            have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
            obtain ⟨rrC, labeledC, bottomTC, hrrC, hcC, hkC, hreadyC, hrecordsC, hranksC,
                htitledC, hfindC⟩ :=
              X_group_bottom_source h0 h hcomp hrun hchildIndex hchildGroup'
            obtain ⟨childOriginal, horigC, hborderC, hpathC, hrecordC, hchildFind'⟩ :=
              X_bottom_constraint_source h0 h hkC hrecordsC hchildIndex
                hchildGroup' hfindC
            have hchildPair : cg.nodes.zipIdx.find? (fun entry =>
                entry.1.border == 2 && entry.1.decl == child.1.decl) =
                some (childOriginal, bottomTC.2) := hchildFind'
            have hpathEq : child.1.clusterPath.dropLast = n.clusterPath := by
              simpa using hchildPathEq
            have hdirect := ranked_compound_child_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB
              hchildZip hchildGroup' hpathEq hchildPair
            have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks child.2 := hdirect.1
            have hne : n.clusterPath ≠ [] := hnonempty idx n hidx hgroup
            have hchildNonEmpty : child.1.clusterPath ≠ [] := by
              intro hempty
              rw [hempty, List.dropLast_nil] at hpathEq
              exact hne hpathEq.symm
            have hlenC : child.1.clusterPath.length = n.clusterPath.length + 1 := by
              rw [← hpathEq, List.length_dropLast]
              have hchildLen := List.length_pos_iff.mpr hchildNonEmpty
              omega
            have hboundChild := hbound child.2 child.1 hchildIndex hchildGroup'
            have hpos : 0 < fuel := by omega
            have hfuelChild : maxLen - child.1.clusterPath.length = fuel - 1 := by omega
            have hcontainsC : child.1.clusterPath.contains ndT.decl = true := by
              have hsub : n.clusterPath <+: child.1.clusterPath := by
                rw [← hpathEq]; exact xcv_dropLast_is_prefix _
              have hmemN : ndT.decl ∈ n.clusterPath :=
                List.contains_iff_mem.mp hcontains
              have hmemC : ndT.decl ∈ child.1.clusterPath :=
                List.Sublist.mem hmemN (List.IsPrefix.sublist hsub)
              exact List.contains_iff_mem.mpr hmemC
            have hih := ih (fuel - 1) (by omega) child.2 child.1 hchildIndex
              hcontainsC hfuelChild
            omega
          | true =>
            have hempty := ranked_empty_group_interval hrr
              (List.mk_mem_zipIdx_iff_getElem?.mpr hidx) hgroup hfindCB hmemCase hchildCase
            have hL : rk rr.ranks idx + 1 ≤ rk rr.ranks bottomTB.2 := hempty
            omega
      · by_cases hdeq : n.decl = ndT.decl
        · have hfindEq : (componentCandidate graph comp candidate).nodes.zipIdx.find?
              (fun entry => entry.1.border == 2 && entry.1.decl == n.decl) =
              some (n, idx) :=
            X_bottom_find_eq h0 h hcomp hidx hbottom
          rw [hdeq] at hfindEq
          have heq : (n, idx) = (ndV, v) :=
            Option.some.inj (hfindEq.symm.trans hbotFindOuter)
          have hiv : idx = v := congrArg Prod.snd heq
          rw [hiv]
          exact Int.le_refl _
        · have hleB : rk run.coordinateProper.rank idx ≤ rk run.coordinateProper.rank v :=
            hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
              hidx hbottom hdeq hcontains
          have e1 : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
            have h1 := xcv_prepared_rk hrr hc hranks
              (List.getElem?_eq_some_iff.mp hidx).1
            exact h1
          omega
  intro idx n hidx hcontains
  have hrr_le := main (maxLen - n.clusterPath.length) idx n hidx hcontains rfl
  have eI : rk run.coordinateProper.rank idx = rk rr.ranks idx := by
    have h1 := xcv_prepared_rk hrr hc hranks
      (List.getElem?_eq_some_iff.mp hidx).1
    exact h1
  omega

private theorem xcv_sideRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hcontains : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
    (hside : q.1.node.border = -1 ∨ q.1.node.border = 1) :
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := xcv_fbs hrun hqget
  have hsideC : nvc.node.border = -1 ∨ nvc.node.border = 1 := by
    rw [hborderEq]; exact hside
  have hncX : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
    rw [hc]; exact hnc
  have hcoordXrfl : (coordinateGraphX P (exactDecls exactIds inp) labeled).rank =
      (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).rank := rfl
  have horiginal := X_side_original hready hncX hsideC
  obtain ⟨top, htopMem, bottom, hfindB, hpathEq, hnn, htonat, hhi⟩ :=
    addClusterBorders_side_rank_bounds _ _ hready horiginal hsideC
  have htopGet : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
  have htopBorder : top.1.node.border = -2 := by
    simpa using (List.mem_filter.mp htopMem).2
  obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
    X_titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
  have htopCgBorder : topOrig.border = -2 := htopBorderEq.symm.trans htopBorder
  have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
    rw [htopRecord]; exact (titleF_keys _).2.2.1
  have hnotProxy : ¬(nvc.node.border = -2 ∨ nvc.node.border = 2) := by
    rintro (h | h) <;> omega
  have hnvcPath : nvc.node.clusterPath = q.1.node.clusterPath :=
    hpathImp hnotProxy
  have htopContains : top.1.node.clusterPath.contains ndT.decl = true := by
    rw [← hpathEq, hnvcPath, ← hdeclT]; exact hcontains
  have htopOrigContains : topOrig.clusterPath.contains ndT.decl = true := by
    rw [← htopPath]; exact htopContains
  have hfindB' : ((titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == topOrig.clusterPath) = some bottom := by
    rw [← htopPath]; exact hfindB
  obtain ⟨origB, horigB, hborderB, hpathB, _, _⟩ :=
    X_bottom_constraint_source h0 h hk hrecords htopCg
      htopCgBorder hfindB'
  have hpathBmem : origB.clusterPath.contains ndT.decl = true := by
    rw [hpathB]; exact htopOrigContains
  have hbotFindOuter : (componentCandidate graph comp candidate).nodes.zipIdx.find?
      (fun entry => entry.1.border == 2 && entry.1.decl == ndT.decl) =
      some (ndV, v) := by
    rw [← hdecl]; exact X_bottom_find_eq h0 h hcomp hvGet hbordV
  have hBle : rk run.coordinateProper.rank bottom.2 ≤
      rk run.coordinateProper.rank v := by
    by_cases hdeq : origB.decl = ndT.decl
    · have hfindBdec := X_bottom_find_eq h0 h hcomp horigB hborderB
      rw [hdeq] at hfindBdec
      have heq := Option.some.inj (hfindBdec.symm.trans hbotFindOuter)
      have hbv : bottom.2 = v := congrArg Prod.snd heq
      rw [hbv]
      exact Int.le_refl _
    · exact hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
        horigB hborderB hdeq hpathBmem
  have hBcoord : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
    have hlt : bottom.2 < (componentCandidate graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp horigB).1
    have h1 := xcv_prepared_rk hrr hc hranks hlt
    exact h1
  have hBtitle : rk (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2 =
      rk rr.ranks bottom.2 := by
    have h1 := xcv_titled_rk (P := P) (exact := exactDecls exactIds inp) hrr hranks
      (List.getElem?_eq_some_iff.mp horigB).1
    exact h1.1
  have hBnn : 0 ≤ rk rr.ranks bottom.2 := rankWithBudget_rk_nonneg hrr bottom.2
  have hbotnn : 0 ≤ rk run.coordinateProper.rank bottom.2 := by
    rw [hBcoord]; exact hBnn
  have htonat : (rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2).toNat ≤
      (rk run.coordinateProper.rank bottom.2).toNat := by
    rw [hcoordXrfl, hBcoord, ← hBtitle]; exact hhi
  have hqb : rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2 ≤
      rk run.coordinateProper.rank bottom.2 :=
    xcv_toNat_le_of_nonneg hnn hbotnn htonat
  have hq : rk run.coordinateProper.rank q.2 ≤
      rk run.coordinateProper.rank bottom.2 := by
    have hQ : rk run.coordinateProper.rank q.2 =
        rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank q.2 := by
      rw [hc]
    rw [hQ]; exact hqb
  exact Int.le_trans hq hBle

private theorem xcv_titleRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    (hnest : Xb_NestedExact exactIds)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hcontains : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true)
    (hb3 : q.1.node.border = 3) :
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, hpathImp⟩ := xcv_fbs hrun hqget
  have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
    rw [hc]; exact hnc
  have hb3C : nvc.node.border = 3 := by rw [hborderEq]; exact hb3
  obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath,
      htitleRank⟩ :=
    xcv_title_rank_source hk hshape haligned hncL hb3C
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
    have hle := xcv_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT hdecl
      hnest hn hncN
    have hrankEq : rk run.coordinateProper.rank q.2 = rk labeled.rank originalIndex := by
      rw [← hc]; exact htitleRank
    have hlabEq : rk labeled.rank originalIndex =
        rk run.coordinateProper.rank originalIndex := by
      have h1 : originalIndex < labeled.nodes.length :=
        (List.getElem?_eq_some_iff.mp horiginal).1
      exact (xcv_coord_rank_eq hc haligned h1).symm
    rw [hrankEq, hlabEq]; exact hle
  · exact absurd (hdT.symm.trans hOrigReal) (by decide)
private theorem xcv_memberRankLe {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl) :
    ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
    q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v := by
  have hnest : Xb_NestedExact exactIds := Xb_NestedExact_holds exactIds
  have hdeclT : ((componentCandidate graph comp candidate).nodes.getD t default).decl =
      ndT.decl := by
    rw [List.getD_eq_getElem?_getD, htGet, Option.getD_some]
  intro q hq hcontains
  have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvc, hnc, hborderEq, _, _⟩ := xcv_fbs hrun hqget
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hncL : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[q.2]? = some nvc := by
    rwa [← hc] at hnc
  rcases xcv_coord_lookup P (exactDecls exactIds inp) labeled hncL with
    ⟨m, hm, hmd, hb, hp, -⟩ | hside | ⟨_, _, _, _, _, hb3, _⟩
  · by_cases hqd : q.1.dummy = true
    · exact X_bottomDummyRankLe exactIds hnest h0 h hlines hwf hframed hcomp hrun hvGet htGet
        hbordV hbordT hdecl q hq hcontains hqd
    · have hqdF : q.1.dummy = false := by simpa using hqd
      by_cases hbS : nvc.node.border = -1 ∨ nvc.node.border = 1 ∨ nvc.node.border = 3
      · have hqbS : q.1.node.border = -1 ∨ q.1.node.border = 1 ∨
            q.1.node.border = 3 := by
          rcases hbS with h | h | h
          · exact Or.inl (by rw [← hborderEq]; exact h)
          · exact Or.inr (Or.inl (by rw [← hborderEq]; exact h))
          · exact Or.inr (Or.inr (by rw [← hborderEq]; exact h))
        rcases hqbS with hb1 | hb2 | hb3q
        · exact xcv_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
            hdecl hnest q hq hcontains (Or.inl hb1)
        · exact xcv_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
            hdecl hnest q hq hcontains (Or.inr hb2)
        · exact xcv_titleRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
            hdecl hnest q hq hcontains hb3q
      · by_cases hbP : nvc.node.border = -2 ∨ nvc.node.border = 2
        · obtain ⟨owner, span, _, _, hproper, _, _⟩ := xcv_proxy_interval hrun hnc hbP
          have hqq : q.1 =
              { nvc with node := { nvc.node with w := span.hi - span.lo } } :=
            Option.some.inj (hqget.symm.trans hproper)
          have hdu : nvc.dummy = q.1.dummy := by rw [hqq]
          have hmdF : m.dummy = false := by rw [← hmd, hdu]; exact hqdF
          have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
          rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
          · have hncN : n.clusterPath.contains ndT.decl = true := by
              rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
            exact xcv_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
              hdecl hnest hn hncN
          · rw [hdT] at hmdF
            simp at hmdF
        · obtain ⟨hrecFull, -⟩ := xcv_nonproxy hrun hnc hbP
          have hqq : q.1 = nvc := Option.some.inj (hqget.symm.trans hrecFull)
          have hmdF : m.dummy = false := by rw [← hmd, ← hqq]; exact hqdF
          have hpathT : nvc.node.clusterPath = q.1.node.clusterPath := by rw [hqq]
          rcases hk q.2 m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
          · have hncN : n.clusterPath.contains ndT.decl = true := by
              rw [← hnp, ← hp hmdF, hpathT, ← hdeclT]; exact hcontains
            exact xcv_origRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
              hdecl hnest hn hncN
          · rw [hdT] at hmdF
            simp at hmdF
  · rcases hside.2 with hb1 | hb2
    · exact xcv_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
        hdecl hnest q hq hcontains (Or.inl (by rw [← hborderEq]; exact hb1))
    · exact xcv_sideRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
        hdecl hnest q hq hcontains (Or.inr (by rw [← hborderEq]; exact hb2))
  · exact xcv_titleRankLe h0 h hlines hwf hframed hcomp hrun hvGet htGet hbordV hbordT
      hdecl hnest q hq hcontains (by rw [← hborderEq]; exact hb3)

private theorem xcv_memberBottom {P : Params} {inp : Input} {exactIds : List String}
    {graph : Graph} {comp : List Nat}
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {v t : Nat}
    (hvLen : v < run.proper.nodes.length)
    (hcoordV : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes.getD v default))
    (hbV : (run.coordinateProper.nodes.getD v default).node.border = 2)
    (hrank : ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains
        ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
      rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v) :
    ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains
        ((componentCandidate graph comp candidate).nodes.getD t default).decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none),
    r.y + r.h ≤ run.ys.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hrankEq : ∀ x, rk run.proper.rank x = rk run.coordinateProper.rank x :=
    fun x => X_proper_rank_eq_local hrun x
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, htopShift, hysShift⟩ := xcv_shift_eqs hrun
  have hcyLen : y_pre.length = run.coordinateProper.nodes.length :=
    (CoordsImpl.rankCoordsWith_length hry).1
  have hysLen : ys_pre.length = run.coordinateProper.nodes.length := by
    rw [← hyspre]
    unfold proxyYs
    rw [List.length_map, List.length_zipIdx]
    exact hcyLen
  have hvC : v < run.coordinateProper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hcoordV).1
  have hvPre : v < y_pre.length := by omega
  have hvYs : v < ys_pre.length := by omega
  have hpg := proxyYs_getD run.coordinateProper run.layers top_pre y_pre hcoordV hvPre
  rw [hyspre] at hpg
  have hbeqF : ((run.coordinateProper.nodes.getD v default).node.border == -2) =
      false := by rw [hbV]; simp
  have hbeqT : ((run.coordinateProper.nodes.getD v default).node.border == 2) =
      true := by rw [hbV]; simp
  have n1 : ¬(((run.coordinateProper.nodes.getD v default).node.border == -2) = true) := by
    rw [hbeqF]; decide
  have p2 : ((run.coordinateProper.nodes.getD v default).node.border == 2) = true := by
    rw [hbeqT]
  rw [ite_eq_right n1, ite_eq_left p2] at hpg
  have hlayV0 := hcov v hvLen
  rw [hrankEq v] at hlayV0
  obtain ⟨lv, hlyV, -, -⟩ := hlayV0
  have hrVlt : (rk run.coordinateProper.rank v).toNat < top_pre.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hlyV).1
    have h2 : top_pre.length = run.layers.length :=
      (CoordsImpl.rankCoordsWith_length hry).2
    omega
  have hrkv : (run.coordinateProper.rank.getD v 0).toNat =
      (rk run.coordinateProper.rank v).toNat := rfl
  have htopV := htopShift _ hrVlt
  have hysVeq := hysShift v hvYs
  rw [hrkv] at hysVeq
  have hYsV : run.ys.getD v 0 = run.top.getD (rk run.coordinateProper.rank v).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
    rw [hysVeq, htopV, hpg]
    omega
  have hbands := X_ReserveBands_holds exactIds hrun
  intro r hr
  obtain ⟨q, hq, hqr⟩ := List.mem_filterMap.mp hr
  have hc : q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true := by
    by_cases h : q.1.node.clusterPath.contains
        ((componentCandidate graph comp candidate).nodes.getD t default).decl = true
    · exact h
    · have hf : q.1.node.clusterPath.contains
          ((componentCandidate graph comp candidate).nodes.getD t default).decl = false :=
        Bool.eq_false_iff.mpr h
      rw [hf] at hqr
      simp at hqr
  have hqr' : Labels.rectAt run.proper run.xs run.ys q.2 = r := by
    rw [hc] at hqr
    simpa using hqr
  have hlen : q.2 < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)).1
  have hvCq : q.2 < run.coordinateProper.nodes.length := by omega
  have hlayQ0 := hcov q.2 hlen
  rw [hrankEq q.2] at hlayQ0
  obtain ⟨lq, hlyQ, hvInQ, hrknnQ⟩ := hlayQ0
  have hrkQnn : 0 ≤ rk run.coordinateProper.rank q.2 := hrknnQ
  have hrkQ : rk run.coordinateProper.rank q.2 =
      ((rk run.coordinateProper.rank q.2).toNat : Int) := by omega
  have hband := (hbands.1 _ _ _ hlyQ hvInQ hvCq hrkQ).2
  have hrk := hrank q hq hc
  have hqq := xcv_rkToNat_le hrkQnn hrk
  have hlyQD : run.layers.getD (rk run.coordinateProper.rank q.2).toNat [] = lq := by
    rw [List.getD_eq_getElem?_getD, hlyQ]; rfl
  have hle : run.top.getD (rk run.coordinateProper.rank q.2).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper lq ≤ run.ys.getD v 0 := by
    by_cases heq : (rk run.coordinateProper.rank q.2).toNat =
        (rk run.coordinateProper.rank v).toNat
    · have htopEq : run.top.getD (rk run.coordinateProper.rank q.2).toNat 0 =
          run.top.getD (rk run.coordinateProper.rank v).toNat 0 := by rw [heq]
      have hlayerEq : CoordsImpl.layerHeight run.coordinateProper lq =
          CoordsImpl.layerHeight run.coordinateProper
            (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
        rw [← hlyQD, heq]
      rw [htopEq, hlayerEq, hYsV]
      exact Int.le_refl _
    · have hlt : (rk run.coordinateProper.rank q.2).toNat <
          (rk run.coordinateProper.rank v).toNat := by omega
      have hdisj := hbands.2 _ _ _ _ hlt hlyQ hlyV
      have hnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lv :=
        CoordsImpl.layerHeight_nonneg _ _
      have hlyVD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
        rw [List.getD_eq_getElem?_getD, hlyV]; rfl
      rw [hYsV, hlyVD]
      omega
  rw [← hqr']
  have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨nvcQ, hncQ, _, hHEqQ, _⟩ := xcv_fbs hrun hqget
  have hnodeHq : RouteImpl.nodeH run.proper q.2 = CoordsImpl.nodeH run.coordinateProper q.2 := by
    have e1 : RouteImpl.nodeH run.proper q.2 = q.1.node.h := by simp only [RouteImpl.nodeH, hqget]
    have e2 : CoordsImpl.nodeH run.coordinateProper q.2 = nvcQ.node.h := by
      simp only [CoordsImpl.nodeH, hncQ]
    rw [e1, e2, hHEqQ]
  show RouteImpl.yAt run.ys q.2 + RouteImpl.nodeH run.proper q.2 ≤ _
  rw [hnodeHq]
  exact Int.le_trans hband hle

private theorem exactGroupFrameStrict_top {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node} {parentBox childBox : ModelBox}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hpb : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hcb : child.border = -2)
    (hpbox : inp.boxes[parent.decl]? = some parentBox)
    (hcbox : inp.boxes[child.decl]? = some childBox)
    (href : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).y <
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).y := by
  have hlines := execution.lines_length
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨parentBottom, hparentBottom⟩ :=
    X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines hcomp hparent hpb
  obtain ⟨childBottom, hchildBottom⟩ :=
    X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines hcomp hchild hcb
  have hpath := xcv_direct_group_path execution hwf hparent hpb hchild hcb hpbox hcbox href hne
  have htopMem : ((parent, parentIndex) : Node × Nat) ∈ cg.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hparent
  have hchildMem : ((child, childIndex) : Node × Nat) ∈ cg.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hchild
  have hinterv := ranked_compound_child_interval hrr htopMem hpb hparentBottom
    hchildMem hcb hpath hchildBottom
  have hintervTop : rk rr.ranks parentIndex + 1 ≤ rk rr.ranks childIndex := hinterv.1
  have hparentLt : parentIndex < cg.nodes.length := (List.getElem?_eq_some_iff.mp hparent).1
  have hchildLt : childIndex < cg.nodes.length := (List.getElem?_eq_some_iff.mp hchild).1
  have eTopP : rk run.coordinateProper.rank parentIndex = rk rr.ranks parentIndex :=
    xcv_prepared_rk hrr hc hranks hparentLt
  have eTopC : rk run.coordinateProper.rank childIndex = rk rr.ranks childIndex :=
    xcv_prepared_rk hrr hc hranks hchildLt
  have rEqP : rk run.proper.rank parentIndex = rk run.coordinateProper.rank parentIndex :=
    X_proper_rank_eq_local hrun parentIndex
  have hrankEq : ∀ x, rk run.proper.rank x = rk run.coordinateProper.rank x :=
    fun x => X_proper_rank_eq_local hrun x
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hrouteOk := (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hrouteOk).2.2.2.1
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
    rw [hnodes]; exact (proxyWidths_rel hproxy).2.2.1
  have hparentLen : parentIndex < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun parentIndex hparentLt
  have hchildLen : childIndex < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun childIndex hchildLt
  have hCgpos : parentIndex < run.coordinateProper.nodes.length := by omega
  obtain ⟨tcoordP, htcoordP, htbP, _, htpathP, htcoordH⟩ :=
    xcv_top_coord execution.graph0_eq execution.graph_eq hcomp hrun hparent hpb
  obtain ⟨tpropP, htpropP, htpropPP⟩ :=
    xcv_top_proper hrun htcoordP htbP
  have hdeclP : parent.clusterPath.contains parent.decl = true := by
    obtain ⟨_, _, hpathG⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq hparent hpb
    rw [hpathG]; simp
  have htcontainsP : tpropP.node.clusterPath.contains parent.decl = true := by
    rw [htpropPP, htpathP]; exact hdeclP
  have hgroupGetP : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hgroupGetC : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hframeGroupP : (cg.nodes.getD parentIndex default).border = -2 := by
    rw [hgroupGetP]; exact hpb
  have htqmemP : (tpropP, parentIndex) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htpropP
  have htcontainsP' : (tpropP, parentIndex).1.node.clusterPath.contains
      (cg.nodes.getD parentIndex default).decl = true := by
    rw [hgroupGetP]; exact htcontainsP
  have htopLe : (frameRect execution.params cg run parentIndex).y ≤
      (Labels.rectAt run.proper run.xs run.ys parentIndex).y :=
    (frameRect_member_vertical (P := execution.params) (cg := cg) (run := run)
      (i := parentIndex) (q := (tpropP, parentIndex)) hframeGroupP htqmemP htcontainsP').1
  obtain ⟨ltP, hlyP, hmemT, hnnP⟩ := hcov parentIndex hparentLen
  rw [rEqP] at hlyP hnnP
  have htopC : ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains child.decl = true →
      rk run.proper.rank childIndex ≤ rk run.proper.rank q.2 := by
    intro q hq hcontains
    have hget := List.mem_zipIdx_iff_getElem?.mp hq
    have hlen := (List.getElem?_eq_some_iff.mp hget).1
    exact (x_topRank_holds exactIds) execution.graph0_eq execution.graph_eq hlines hwf hfp
      hcomp hrun hchild hcb hchildLt hlen (by
        simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some, hcontains])
  let childRects := run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  obtain ⟨cbV, cbNdV, hcbGet, hcbBord, hcbDecl⟩ :=
    xcv_bottom_marker execution.graph0_eq execution.graph_eq hcomp hrun hchild hcb
  have hcbHull : Labels.rectAt run.proper run.xs run.ys cbV ∈ childRects :=
    xcv_bottom_hull_mem execution.graph0_eq execution.graph_eq hcomp hrun hchild hcb
      hcbGet hcbBord hcbDecl
  have hnonempty : childRects ≠ [] := by
    intro hempty
    rw [hempty] at hcbHull
    exact List.not_mem_nil hcbHull
  have hTopY_P : (Labels.rectAt run.proper run.xs run.ys parentIndex).y =
      run.ys.getD parentIndex 0 := rfl
  obtain ⟨hinBand, _⟩ := X_ReserveBands_holds exactIds hrun
  have hnodeHT : CoordsImpl.nodeH run.coordinateProper parentIndex = 0 := by
    simp only [CoordsImpl.nodeH, htcoordP]
    exact htcoordH
  have hrkT : rk run.coordinateProper.rank parentIndex =
      ((rk run.coordinateProper.rank parentIndex).toNat : Int) := by omega
  have hbandT := (hinBand _ _ _ hlyP hmemT hCgpos hrkT).2
  rw [hnodeHT] at hbandT
  have hgap := xcv_post_gap hrun
  have hall : ∀ rect ∈ childRects,
      (Labels.rectAt run.proper run.xs run.ys parentIndex).y < rect.y := by
    intro rect hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcontains
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      have hle : rk run.proper.rank childIndex ≤ rk run.proper.rank entry.2 :=
        htopC entry hentry hcontains
      have hqLen : entry.2 < run.proper.nodes.length :=
        (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hentry)).1
      have hqC : entry.2 < run.coordinateProper.nodes.length := by omega
      obtain ⟨lQ, hlyQ, hmemQ, hnnQ⟩ := hcov entry.2 hqLen
      rw [hrankEq entry.2] at hlyQ hnnQ
      have hltQ : (rk run.coordinateProper.rank parentIndex).toNat <
          (rk run.coordinateProper.rank entry.2).toNat := by
        have h6 : rk run.coordinateProper.rank childIndex ≤
            rk run.coordinateProper.rank entry.2 := by
          rw [← hrankEq childIndex, ← hrankEq entry.2]; exact hle
        omega
      have hrkQ : rk run.coordinateProper.rank entry.2 =
          ((rk run.coordinateProper.rank entry.2).toNat : Int) := by omega
      have hbandQlo := (hinBand _ _ _ hlyQ hmemQ hqC hrkQ).1
      have hgapTQ := hgap _ _ _ _ hltQ hlyP hlyQ
      have hYq : (Labels.rectAt run.proper run.xs run.ys entry.2).y =
          run.ys.getD entry.2 0 := rfl
      omega
    · cases heq
  have hmin : (Labels.rectAt run.proper run.xs run.ys parentIndex).y <
      (boundsOf childRects []).minY :=
    xcv_strict_minY _ _ hall hnonempty
  have hchildY : (frameRect execution.params cg run childIndex).y =
      (boundsOf childRects []).minY := by
    simp only [childRects, frameRect, hgroupGetC, hcb,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hTopDone : (frameRect execution.params cg run parentIndex).y <
      (frameRect execution.params cg run childIndex).y := by
    omega
  exact hTopDone
private theorem xcv_shifts_nonneg_aux (es : List Int) (s : Int) (out : List Int)
    (hpos : ∀ e ∈ es, 0 ≤ e) (hs : 0 ≤ s) (hout : ∀ x ∈ out, 0 ≤ x) :
    ∀ x ∈ ((es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2), 0 ≤ x := by
  induction es generalizing s out with
  | nil => simpa using hout
  | cons e es ih =>
    have he : 0 ≤ e := hpos e List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih
    · intro e' he'
      exact hpos e' (List.mem_cons_of_mem e he')
    · omega
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hout x hx
      · exact hs

private theorem xcv_shifts_nonneg (extra shifts : List Int)
    (hpos : ∀ e ∈ extra, 0 ≤ e)
    (hshifts : shifts =
      (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2) :
    ∀ i, 0 ≤ shifts.getD i 0 := by
  intro i
  subst hshifts
  by_cases hi : i < (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
      (0, ([] : List Int))).2.length
  · have hmem : ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
        (0, ([] : List Int))).2)[i]'hi ∈
        (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
          (0, ([] : List Int))).2 :=
      List.mem_of_getElem? (List.getElem?_eq_getElem hi)
    have h := xcv_shifts_nonneg_aux extra 0 [] hpos (Int.le_refl 0) (by simp) _ hmem
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa using h
  · have hg : ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
        (0, ([] : List Int))).2)[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    rw [List.getD_eq_getElem?_getD, hg]
    simp
private theorem xcv_top_nonneg {P : Params} {inp : Input}
    {exactIds : List String}
    {graph : Graph}
    {comp : List Nat}
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    ∀ k, 0 ≤ run.top.getD k 0 := by
  obtain ⟨y_pre, top_pre, ys_pre, hry, hyspre, hreserve, hcoordYs⟩ := xcv_run_pre hrun
  have htopLen : top_pre.length = run.layers.length := (CoordsImpl.rankCoordsWith_length hry).2
  have hpre : ∀ k, 0 ≤ top_pre.getD k 0 := by
    obtain ⟨hg, hslot, _, hsnn, _, htop, _⟩ := CoordsImpl.rankCoordsWith_spec hry
    have hheights : ∀ x ∈ run.layers.map (CoordsImpl.layerHeight run.coordinateProper),
        0 ≤ x := by
      intro x hx
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
      exact CoordsImpl.layerHeight_nonneg _ _
    have hsteps : ∀ x ∈ CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)), 0 ≤ x :=
      CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hsnn
    intro k
    rw [htop, List.getD_eq_getElem?_getD]
    cases hk : (CoordsImpl.topsFrom 0 1 0
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
        (CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
          (run.routing.gaps.map (·.slots))))[k]? with
    | none => exact Int.le_refl 0
    | some t =>
      exact fbs_topsFrom01_nonneg _ _ _ (Int.le_refl 0) hheights hsteps t
        (List.mem_of_getElem? hk)
  unfold reserveExactRanks at hreserve
  obtain ⟨topNew, htopM, h1⟩ := xcv_bind_ok hreserve
  obtain ⟨ysNew, hysM, h2⟩ := xcv_bind_ok h1
  have hpair := Except.ok.inj h2
  have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
  rw [htopNew_eq] at htopM
  have hextra := xcv_extra_fold (componentCandidate graph comp candidate)
    (exactDecls exactIds inp) labels run.coordinateProper ys_pre top_pre
    (run.layers.map fun layer => layer.foldl (fun h v => max h (RouteImpl.nodeH run.coordinateProper v)) 0)
  have hposM : ∀ e ∈ (componentCandidate graph comp candidate).nodes.zipIdx.foldl
      (fun (acc : List Int) (q : Node × Nat) =>
        if !(exactDecls exactIds inp).contains q.1.decl then acc
        else
          let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
            (componentCandidate graph comp candidate).slot
          if sizes.isEmpty then acc
          else
            let rank := (run.coordinateProper.rank.getD q.2 0).toNat
            let reserved := max q.1.h ((sizes.length : Int) * Loops.band
              (componentCandidate graph comp candidate).slot sizes)
            let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
              (run.layers.map fun layer => layer.foldl (fun h v => max h
                (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
            acc.set rank (max (acc.getD rank 0) needed))
      (List.replicate top_pre.length (0 : Int)), 0 ≤ e := by
    intro e he
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    have h := hextra.2 i
    rw [List.getD_eq_getElem?_getD, hi] at h
    simp at h
    exact h
  have htop_eq : ∀ (r : Nat), r < top_pre.length → run.top.getD r 0 =
      top_pre.getD r 0 +
        (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
          (fun (acc : List Int) (q : Node × Nat) =>
            if !(exactDecls exactIds inp).contains q.1.decl then acc
            else
              let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
                (componentCandidate graph comp candidate).slot
              if sizes.isEmpty then acc
              else
                let rank := (run.coordinateProper.rank.getD q.2 0).toNat
                let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                  (componentCandidate graph comp candidate).slot sizes)
                let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                  (run.layers.map fun layer => layer.foldl (fun h v => max h
                    (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
                acc.set rank (max (acc.getD rank 0) needed))
          (List.replicate top_pre.length (0 : Int))).foldl
          (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD r 0 := by
    intro r hr
    have hrZ : r < (top_pre.zipIdx).length := by
      rw [List.length_zipIdx]
      exact hr
    have hzin : (top_pre.zipIdx)[r]? = some (top_pre[r], r) := by
      have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
      simp [List.getElem?_zipIdx, h1]
    obtain ⟨hlenM, hidx⟩ := mapM_getElem? _ _ _ htopM
    obtain ⟨b, hb, hbr⟩ := hidx r _ hzin
    have hbeq := Measure.checkedI32_ok hb
    have h1 : top_pre[r]? = some top_pre[r] := List.getElem?_eq_getElem hr
    have e3 : top_pre.getD r 0 = top_pre[r] := by
      rw [List.getD_eq_getElem?_getD, h1]
      rfl
    have e4 : run.top.getD r 0 = b := by
      rw [List.getD_eq_getElem?_getD, hbr]
      rfl
    rw [e4, e3]
    exact hbeq
  intro k
  by_cases hk : k < top_pre.length
  · rw [htop_eq k hk]
    have h1 := hpre k
    have h2 : 0 ≤ (((componentCandidate graph comp candidate).nodes.zipIdx.foldl
        (fun (acc : List Int) (q : Node × Nat) =>
          if !(exactDecls exactIds inp).contains q.1.decl then acc
          else
            let sizes := loopSizes (componentCandidate graph comp candidate).edges labels q.2
              (componentCandidate graph comp candidate).slot
            if sizes.isEmpty then acc
            else
              let rank := (run.coordinateProper.rank.getD q.2 0).toNat
              let reserved := max q.1.h ((sizes.length : Int) * Loops.band
                (componentCandidate graph comp candidate).slot sizes)
              let needed := ys_pre.getD q.2 0 + reserved - top_pre.getD rank 0 -
                (run.layers.map fun layer => layer.foldl (fun h v => max h
                  (RouteImpl.nodeH run.coordinateProper v)) 0).getD rank 0
              acc.set rank (max (acc.getD rank 0) needed))
        (List.replicate top_pre.length (0 : Int))).foldl
        (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2.getD k 0 :=
      xcv_shifts_nonneg _ _ hposM rfl k
    omega
  · have hlen : run.top.length = top_pre.length := by
      obtain ⟨hlenM, _⟩ := mapM_getElem? _ _ _ htopM
      have hz : (top_pre.zipIdx).length = top_pre.length := by simp
      omega
    have hg : run.top[k]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [List.getD_eq_getElem?_getD, hg]
    simp

private theorem exactGroupFrameStrict_bottom {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node} {parentBox childBox : ModelBox}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hpb : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hcb : child.border = -2)
    (hpbox : inp.boxes[parent.decl]? = some parentBox)
    (hcbox : inp.boxes[child.decl]? = some childBox)
    (href : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).h <
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).y +
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).h := by
  have hlines := execution.lines_length
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨parentBottom, hparentBottom⟩ :=
    X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines hcomp hparent hpb
  obtain ⟨childBottom, hchildBottom⟩ :=
    X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines hcomp hchild hcb
  have hpath := xcv_direct_group_path execution hwf hparent hpb hchild hcb hpbox hcbox href hne
  have htopMem : ((parent, parentIndex) : Node × Nat) ∈ cg.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hparent
  have hchildMem : ((child, childIndex) : Node × Nat) ∈ cg.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hchild
  have hinterv := ranked_compound_child_interval hrr htopMem hpb hparentBottom
    hchildMem hcb hpath hchildBottom
  have hintervBot : rk rr.ranks childBottom.2 + 1 ≤ rk rr.ranks parentBottom.2 :=
    hinterv.2
  have hgroupGetC : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hgroupGetP : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hbotMemC : childBottom ∈ cg.nodes.zipIdx :=
    List.mem_of_find?_eq_some hchildBottom
  have hbotLookupC : cg.nodes[childBottom.2]? = some childBottom.1 :=
    List.mem_zipIdx_iff_getElem?.mp hbotMemC
  have hcbLt : childBottom.2 < cg.nodes.length :=
    (List.getElem?_eq_some_iff.mp hbotLookupC).1
  have hbotMemP : parentBottom ∈ cg.nodes.zipIdx :=
    List.mem_of_find?_eq_some hparentBottom
  have hbotLookupP : cg.nodes[parentBottom.2]? = some parentBottom.1 :=
    List.mem_zipIdx_iff_getElem?.mp hbotMemP
  have hpbLt : parentBottom.2 < cg.nodes.length :=
    (List.getElem?_eq_some_iff.mp hbotLookupP).1
  have eCB : rk run.coordinateProper.rank childBottom.2 = rk rr.ranks childBottom.2 :=
    xcv_prepared_rk hrr hc hranks hcbLt
  have ePB : rk run.coordinateProper.rank parentBottom.2 = rk rr.ranks parentBottom.2 :=
    xcv_prepared_rk hrr hc hranks hpbLt
  have hrankEq : ∀ x, rk run.proper.rank x = rk run.coordinateProper.rank x :=
    fun x => X_proper_rank_eq_local hrun x
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hrouteOk := (RouteImpl.routeWithLanes_geometry hroute).1
  have hcov := (RouteImpl.layersOk_spec hrouteOk).2.2.2.1
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
    rw [hnodes]; exact (proxyWidths_rel hproxy).2.2.1
  have hcbLen : childBottom.2 < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun childBottom.2 hcbLt
  have hpbLen : parentBottom.2 < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun parentBottom.2 hpbLt
  have hcondCB := List.find?_some hchildBottom
  simp only [Bool.and_eq_true, beq_iff_eq] at hcondCB
  obtain ⟨hbordCB, hdeclCB⟩ := hcondCB
  have hcondPB := List.find?_some hparentBottom
  simp only [Bool.and_eq_true, beq_iff_eq] at hcondPB
  obtain ⟨hbordPB, hdeclPB⟩ := hcondPB
  obtain ⟨bcoordC, hbcoordC, hbbC, _, hbpathC, bh0C⟩ :=
    xcv_bottom_coord execution.graph0_eq execution.graph_eq hcomp hrun hbotLookupC hbordCB
  obtain ⟨bpropC, hbpropC, hbpropPC, hnodeH_C⟩ :=
    xcv_bottom_proper hrun hbcoordC hbbC bh0C
  obtain ⟨bcoordP, hbcoordP, hbbP, _, hbpathP, bh0P⟩ :=
    xcv_bottom_coord execution.graph0_eq execution.graph_eq hcomp hrun hbotLookupP hbordPB
  obtain ⟨bpropP, hbpropP, hbpropPP, hnodeH_P⟩ :=
    xcv_bottom_proper hrun hbcoordP hbbP bh0P
  obtain ⟨boxC, _, hpathBoxC⟩ :=
    X_cg_bottom_box execution.graph0_eq execution.graph_eq hbotLookupC hbordCB
  have hdeclBC : childBottom.1.clusterPath.contains childBottom.1.decl = true := by
    rw [hpathBoxC]; simp
  obtain ⟨boxP, _, hpathBoxP⟩ :=
    X_cg_bottom_box execution.graph0_eq execution.graph_eq hbotLookupP hbordPB
  have hdeclBP : parentBottom.1.clusterPath.contains parentBottom.1.decl = true := by
    rw [hpathBoxP]; simp
  have hbcontainsC : bpropC.node.clusterPath.contains child.decl = true := by
    rw [hbpropPC, hbpathC, ← hdeclCB]; exact hdeclBC
  have hbcontainsP : bpropP.node.clusterPath.contains parent.decl = true := by
    rw [hbpropPP, hbpathP, ← hdeclPB]; exact hdeclBP
  have hframeGroupP : (cg.nodes.getD parentIndex default).border = -2 := by
    rw [hgroupGetP]; exact hpb
  have hbqmemP : (bpropP, parentBottom.2) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hbpropP
  have hbcontainsP' : (bpropP, parentBottom.2).1.node.clusterPath.contains
      (cg.nodes.getD parentIndex default).decl = true := by
    rw [hgroupGetP]; exact hbcontainsP
  have hparentGe : (Labels.rectAt run.proper run.xs run.ys parentBottom.2).y +
        (Labels.rectAt run.proper run.xs run.ys parentBottom.2).h ≤
      (frameRect execution.params cg run parentIndex).y +
        (frameRect execution.params cg run parentIndex).h :=
    (frameRect_member_vertical (P := execution.params) (cg := cg) (run := run)
      (i := parentIndex) (q := (bpropP, parentBottom.2))
      hframeGroupP hbqmemP hbcontainsP').2
  have hBotYH_P : (Labels.rectAt run.proper run.xs run.ys parentBottom.2).y +
      (Labels.rectAt run.proper run.xs run.ys parentBottom.2).h =
      run.ys.getD parentBottom.2 0 := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
    simp [hnodeH_P]
  have hCvC : childBottom.2 < run.coordinateProper.nodes.length := by omega
  have hCvP : parentBottom.2 < run.coordinateProper.nodes.length := by omega
  obtain ⟨lCB, hlyCB, hmemCB, hnnCB⟩ := hcov childBottom.2 hcbLen
  rw [hrankEq childBottom.2] at hlyCB hnnCB
  obtain ⟨lPB, hlyPB, hmemPB, hnnPB⟩ := hcov parentBottom.2 hpbLen
  rw [hrankEq parentBottom.2] at hlyPB hnnPB
  obtain ⟨hinBand, _⟩ := X_ReserveBands_holds exactIds hrun
  have hrkCB : rk run.coordinateProper.rank childBottom.2 =
      ((rk run.coordinateProper.rank childBottom.2).toNat : Int) := by omega
  have hrkPB : rk run.coordinateProper.rank parentBottom.2 =
      ((rk run.coordinateProper.rank parentBottom.2).toNat : Int) := by omega
  have hnodeHCb : CoordsImpl.nodeH run.coordinateProper childBottom.2 = 0 := by
    simp only [CoordsImpl.nodeH, hbcoordC]; exact bh0C
  have hbandCBhi := (hinBand _ _ _ hlyCB hmemCB hCvC hrkCB).2
  rw [hnodeHCb] at hbandCBhi
  have hbandPBlo := (hinBand _ _ _ hlyPB hmemPB hCvP hrkPB).1
  have hltCB : (rk run.coordinateProper.rank childBottom.2).toNat <
      (rk run.coordinateProper.rank parentBottom.2).toNat := by omega
  have hgapCB := (xcv_post_gap hrun) _ _ _ _ hltCB hlyCB hlyPB
  have hChildLtParent : run.ys.getD childBottom.2 0 < run.ys.getD parentBottom.2 0 := by
    omega
  have hzero : 0 ≤ run.ys.getD childBottom.2 0 := by
    have hnn := xcv_top_nonneg hrun (rk run.coordinateProper.rank childBottom.2).toNat
    have hlo := (hinBand _ _ _ hlyCB hmemCB hCvC hrkCB).1
    omega
  have hbotC : ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
      q.1.node.clusterPath.contains
        (cg.nodes.getD childIndex default).decl = true →
      rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank childBottom.2 :=
    fun q hq hcontains =>
      xcv_memberRankLe execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp hrun
        hbotLookupC hchild hbordCB hcb hdeclCB q hq hcontains
  have hcoordV : run.coordinateProper.nodes[childBottom.2]? =
      some (run.coordinateProper.nodes.getD childBottom.2 default) := by
    rw [List.getD_eq_getElem?_getD, hbcoordC, Option.getD_some]
  have hbV : (run.coordinateProper.nodes.getD childBottom.2 default).node.border = 2 := by
    have e : run.coordinateProper.nodes.getD childBottom.2 default = bcoordC := by
      simp [List.getD_eq_getElem?_getD, hbcoordC]
    rw [e]; exact hbbC
  let childRects := run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  have hdeclEq : (cg.nodes.getD childIndex default).decl = child.decl := by rw [hgroupGetC]
  have hallUpper : ∀ rect ∈ childRects,
      rect.y + rect.h ≤ run.ys.getD childBottom.2 0 := by
    intro rect hrect
    have hmem' : rect ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD childIndex default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
      rw [hdeclEq]; exact hrect
    exact xcv_memberBottom hrun hcbLen hcoordV hbV hbotC rect hmem'
  have hleMax : (boundsOf childRects []).bottom ≤ run.ys.getD childBottom.2 0 :=
    boundsOf_bottom_le_of_all hzero hallUpper
  have hchildBottomEq : (frameRect execution.params cg run childIndex).y +
      (frameRect execution.params cg run childIndex).h =
      (boundsOf childRects []).bottom :=
    xcv_bottom_frame_eq hchild hcb
  have hparentBottomEq : (frameRect execution.params cg run parentIndex).y +
      (frameRect execution.params cg run parentIndex).h =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains parent.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom :=
    xcv_bottom_frame_eq hparent hpb
  have hBotDone : (frameRect execution.params cg run childIndex).y +
      (frameRect execution.params cg run childIndex).h <
      (frameRect execution.params cg run parentIndex).y +
        (frameRect execution.params cg run parentIndex).h := by
    omega
  exact hBotDone

theorem XCA_LinkTopXW_holds (exactIds : List String) : XCA_LinkTopXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    parentIndex childIndex parent child parentBox childBox hparent hpb hchild hcb hpbox hcbox href hne
  exact exactGroupFrameStrict_top execution.exactFramePrefix hwf hfp hcomp hrun
    hparent hpb hchild hcb hpbox hcbox href hne

theorem XCA_LinkBotXW_holds (exactIds : List String) : XCA_LinkBotXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
    parentIndex childIndex parent child parentBox childBox hparent hpb hchild hcb hpbox hcbox href hne
  exact exactGroupFrameStrict_bottom execution.exactFramePrefix hwf hfp hcomp hrun
    hparent hpb hchild hcb hpbox hcbox href hne

theorem exactGroupFrameStrict {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node} {parentBox childBox : ModelBox}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
    (hpb : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
    (hcb : child.border = -2)
    (hpbox : inp.boxes[parent.decl]? = some parentBox)
    (hcbox : inp.boxes[child.decl]? = some childBox)
    (href : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex) := by
  obtain ⟨hl, hr⟩ := exactGroupFrameStrict_horizontal execution hwf hcomp hrun
    hparent hpb hchild hcb hpbox hcbox href hne
  exact ⟨hl, hr,
    exactGroupFrameStrict_top execution hwf hfp hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne,
    exactGroupFrameStrict_bottom execution hwf hfp hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne⟩

theorem XCA_groupLinkXW_closed (exactIds : List String) :
    XCA_GroupLinkXW exactIds :=
  XCA_groupLinkXW_holds exactIds
    (XCA_LinkLeftXW_holds exactIds)
    (XCA_LinkRightXW_holds exactIds)
    (XCA_LinkTopXW_holds exactIds)
    (XCA_LinkBotXW_holds exactIds)

end PipelineImpl
end Layered
end Elegant
