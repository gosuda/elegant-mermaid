import Elegant.Layered.BottomClearanceInside
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BottomSeamsStructural
import Elegant.Layered.PipelineFacts
import Elegant.Layered.BottomSeamsRank
import Elegant.Layered.Order
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.Labels
import Elegant.Layered.Rank
import Elegant.Layered.Normalize
import Elegant.Layered.SizingFacts
import Elegant.Layered.BracketInsideRankFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Rank-level residual for the dummy-row seam.

A dummy whose node path extends a bottom proxy's cluster path cannot share
that proxy's rank. For executed layouts this is the chain-position fact:
such a dummy lies on the chain of a labelled edge whose tail and head both
contain the proxy's owner (`componentRun_dummy_path_chain_source` with
`commonPath_member_both`), so its rank sits strictly between the endpoint
ranks while `ranked_compound_member_interval` puts both endpoints strictly
below the proxy's bottom marker. It is rank-only (no `leftOf`/`nodeW`),
hence strictly simpler than `dummyInsideProxyRowClear`, and every variable
it constrains is pinned by `comp ∈ components graph` plus
`componentRun … = .ok run`. -/
def DummyNestedRank (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
    ∀ t v : Nat,
      (run.coordinateProper.nodes.getD t default).node.border = 2 →
      (run.coordinateProper.nodes.getD v default).dummy = true →
      (run.coordinateProper.nodes.getD t default).node.clusterPath <+:
        OrderImpl.nodePath run.coordinateProper v →
      rk run.coordinateProper.rank v ≠ rk run.coordinateProper.rank t

/-- An element strictly between two members of an infix `S` of a nodup list
`l` is itself a member of `S`. Copy of the helper in
`BracketInsidePremisesProof` (which keeps it private). -/
private theorem mem_of_between_infix_dm {α : Type} {l S : List α} {a b c : α}
    {li vi ri : Nat}
    (hnd : l.Nodup) (h : S.IsInfix l)
    (ha : a ∈ S) (hb : b ∈ S)
    (hli : l[li]? = some a) (hvi : l[vi]? = some c) (hri : l[ri]? = some b)
    (hlt : li < vi) (hgt : vi < ri) : c ∈ S := by
  obtain ⟨s, t, hs⟩ := h
  subst hs
  have hnd' := List.nodup_append.mp hnd
  have hsS : ∀ x ∈ s, ∀ y ∈ S, x ≠ y :=
    (List.nodup_append.mp hnd'.1).2.2
  have hSt : ∀ x ∈ s ++ S, ∀ y ∈ t, x ≠ y := hnd'.2.2
  have hlen : (s ++ S).length = s.length + S.length := List.length_append ..
  have hliS : s.length ≤ li ∧ li < (s ++ S).length := by
    constructor
    · by_cases hle : s.length ≤ li
      · exact hle
      · have hlt' : li < s.length := by omega
        have hlook : ((s ++ S) ++ t)[li]? = s[li]? := by
          rw [List.getElem?_append_left (by omega),
            List.getElem?_append_left hlt']
        rw [hlook] at hli
        exact (hsS a (List.mem_of_getElem? hli) a ha rfl).elim
    · by_cases hle : (s ++ S).length ≤ li
      · have hlook : ((s ++ S) ++ t)[li]? = t[li - (s ++ S).length]? :=
          List.getElem?_append_right hle
        rw [hlook] at hli
        exact (hSt a (List.mem_append_right s ha) a (List.mem_of_getElem? hli) rfl).elim
      · have hlt' : li < (s ++ S).length := by omega
        exact hlt'
  have hriS : s.length ≤ ri ∧ ri < (s ++ S).length := by
    constructor
    · by_cases hle : s.length ≤ ri
      · exact hle
      · have hlt' : ri < s.length := by omega
        have hlook : ((s ++ S) ++ t)[ri]? = s[ri]? := by
          rw [List.getElem?_append_left (by omega),
            List.getElem?_append_left hlt']
        rw [hlook] at hri
        exact (hsS b (List.mem_of_getElem? hri) b hb rfl).elim
    · by_cases hle : (s ++ S).length ≤ ri
      · have hlook : ((s ++ S) ++ t)[ri]? = t[ri - (s ++ S).length]? :=
          List.getElem?_append_right hle
        rw [hlook] at hri
        exact (hSt b (List.mem_append_right s hb) b (List.mem_of_getElem? hri) rfl).elim
      · have hlt' : ri < (s ++ S).length := by omega
        exact hlt'
  have hviS : s.length ≤ vi ∧ vi < (s ++ S).length := by
    constructor <;> omega
  have hlook : ((s ++ S) ++ t)[vi]? = S[vi - s.length]? := by
    rw [List.getElem?_append_left hviS.2,
      List.getElem?_append_right (by omega : s.length ≤ vi)]
  rw [hlook] at hvi
  exact List.mem_of_getElem? hvi

/-- A dummy strictly between a group's side borders has the group's path as a
prefix of its node path. Same contiguity argument as
`componentRun_inside_prefix`, without the non-dummy hypothesis on `v`. -/
private theorem dummy_interior_prefix {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {pref : List Nat} {layer : List Nat} (hlayer : layer ∈ run.layers)
    {li vpos ri l r v : Nat}
    (hl : layer[li]? = some l) (hv : layer[vpos]? = some v)
    (hr : layer[ri]? = some r)
    (hlt : li < vpos) (hgt : vpos < ri)
    (hlb : (run.coordinateProper.nodes.getD l default).node.border = -1 ∨
      (run.coordinateProper.nodes.getD l default).node.border = 1)
    (hlp : (run.coordinateProper.nodes.getD l default).node.clusterPath = pref)
    (hrb : (run.coordinateProper.nodes.getD r default).node.border = -1 ∨
      (run.coordinateProper.nodes.getD r default).node.border = 1)
    (hrp : (run.coordinateProper.nodes.getD r default).node.clusterPath = pref) :
    pref <+: OrderImpl.nodePath run.coordinateProper v := by
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _⟩ :=
    componentRun_spec hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions =
      .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  have hinfix := OrderImpl.order_clusters_contiguous run.coordinateProper
    orderOptions run.layers horder' layer hlayer pref
  have hnpBorder : ∀ (x : Nat) (nx : ProperNode)
      (hx : run.coordinateProper.nodes[x]? = some nx)
      (hxb : nx.node.border = -1 ∨ nx.node.border = 1)
      (hxp : nx.node.clusterPath = pref),
      OrderImpl.nodePath run.coordinateProper x = pref := by
    intro x nx hx hxb hxp
    obtain ⟨na, hna, hda, _⟩ := OrderImpl.border_node hwf (by
      have hxb' : (run.coordinateProper.nodes.getD x default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD x default).node.border = 1 := by
        rw [show run.coordinateProper.nodes.getD x default = nx from by
          simp [List.getD_eq_getElem?_getD, hx]]
        exact hxb
      exact hxb')
    rw [OrderImpl.nodePath_of_nondummy hna hda]
    have h1 : nx = na := Option.some.inj (hx.symm.trans hna)
    rw [h1] at hxp
    exact hxp
  have hlS : l ∈ layer.filter (fun x =>
      pref.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hl, ?_⟩
    cases hxl : run.coordinateProper.nodes[l]? with
    | none =>
        have hxlD : run.coordinateProper.nodes.getD l default = default := by
          simp [List.getD_eq_getElem?_getD, hxl]
        rw [hxlD] at hlb
        have hd0 : (default : ProperNode).node.border = 0 := rfl
        omega
    | some nl =>
        have hxlD : run.coordinateProper.nodes.getD l default = nl := by
          simp [List.getD_eq_getElem?_getD, hxl]
        have hlb' : nl.node.border = -1 ∨ nl.node.border = 1 := by
          rw [← hxlD]; exact hlb
        have hlp' : nl.node.clusterPath = pref := by
          rw [← hxlD]; exact hlp
        have hnp := hnpBorder l nl hxl hlb' hlp'
        rw [hnp]
        exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hrS : r ∈ layer.filter (fun x =>
      pref.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hr, ?_⟩
    cases hxr : run.coordinateProper.nodes[r]? with
    | none =>
        have hxrD : run.coordinateProper.nodes.getD r default = default := by
          simp [List.getD_eq_getElem?_getD, hxr]
        rw [hxrD] at hrb
        have hd0 : (default : ProperNode).node.border = 0 := rfl
        omega
    | some nr =>
        have hxrD : run.coordinateProper.nodes.getD r default = nr := by
          simp [List.getD_eq_getElem?_getD, hxr]
        have hrb' : nr.node.border = -1 ∨ nr.node.border = 1 := by
          rw [← hxrD]; exact hrb
        have hrp' : nr.node.clusterPath = pref := by
          rw [← hxrD]; exact hrp
        have hnp := hnpBorder r nr hxr hrb' hrp'
        rw [hnp]
        exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hLspec := OrderImpl.orderWithBudget_spec run.coordinateProper
    orderOptions ord horder
  obtain ⟨k, hk, hkl⟩ := List.mem_iff_getElem.mp hlayer
  have hk2 : k < ord.layers.length := by rw [hlayers]; exact hk
  have hndlayer : layer.Nodup := by
    have h := OrderImpl.layer_nodup hLspec.1 hk2
    rw [hlayers] at h
    rw [← hkl, @List.getElem_eq_getD (List Nat) run.layers k hk []]
    exact h
  have hvS : v ∈ layer.filter (fun x =>
      pref.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    have hmem := mem_of_between_infix_dm hndlayer hinfix hlS hrS hl hv hr
      hlt hgt
    exact hmem
  rw [List.mem_filter] at hvS
  exact List.isPrefixOf_iff_prefix.mp hvS.2

/-- The dummy-row clearance seam holds for every executed layout, modulo the
rank-level residual `DummyNestedRank`.

Decision on the assignment's first question: a labelled edge with both
endpoints inside the proxy's group cannot falsify this clause at the same
rank. Its dummy sits strictly between the endpoint ranks
(`Labels.addLabelNode` resizes the midpoint chain node, `span ≥ 2`), while
`ranked_compound_member_interval` puts both endpoints strictly below the
group's own bottom proxy — so `rk v = rk t` is impossible for the proxy's
own group. The same-rank threat is therefore always a cross-group label
(the `DummySameRankRefuted` witness), whose dummy path does not extend the
proxy's path and is ordered outside the bracket. The residual records the
rank half; the prefix half is proved here from contiguity. -/
theorem dummyInsideProxyRowClear_of_execution {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    (hRank : DummyNestedRank execution.params execution.graph) :
    dummyInsideProxyRowClear execution.params execution.graph := by
  have _unused_height : True := trivial
  intro comp hcomp candidate run labels orderOptions hrun t v htborder hdummy
    hheight hrankEq
  have hgraph : measuredGraph execution.params inp o execution.lines =
      .ok execution.graph := execution.graph_eq
  have _hheight' : 0 < RouteImpl.nodeH run.proper v := hheight
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxyEq, hdropEq, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, _, hlengthEq, _, _, _⟩ := proxyWidths_rel hproxyEq
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hlengthEq, ← hdropEq, OrderImpl.dropSynthetic_nodes]
  obtain ⟨proxy, htp⟩ : ∃ x, run.coordinateProper.nodes[t]? = some x := by
    cases hx : run.coordinateProper.nodes[t]? with
    | none =>
        rw [List.getD_eq_getElem?_getD, hx] at htborder
        have hnoneD : (none : Option ProperNode).getD default = default := rfl
        rw [hnoneD] at htborder
        have hd0 : (default : ProperNode).node.border = 0 := rfl
        omega
    | some x => exact ⟨x, rfl⟩
  obtain ⟨other, hv0⟩ : ∃ x, run.coordinateProper.nodes[v]? = some x := by
    cases hx : run.coordinateProper.nodes[v]? with
    | none =>
        exfalso
        have h1 : run.coordinateProper.nodes.length ≤ v :=
          List.getElem?_eq_none_iff.mp hx
        have hlenV : run.proper.nodes.length ≤ v := by
          rw [hnodesLen]; exact h1
        have hnone : run.proper.nodes[v]? = none :=
          List.getElem?_eq_none hlenV
        have hnh : RouteImpl.nodeH run.proper v = 0 := by
          unfold RouteImpl.nodeH
          rw [hnone]
        rw [hnh] at hheight
        omega
    | some x => exact ⟨x, rfl⟩
  have ht' : run.coordinateProper.nodes[t]? = some proxy := htp
  have hv' : run.coordinateProper.nodes[v]? = some other := hv0
  have htGetD : run.coordinateProper.nodes.getD t default = proxy := by
    simp [List.getD_eq_getElem?_getD, ht']
  have hvGetD : run.coordinateProper.nodes.getD v default = other := by
    simp [List.getD_eq_getElem?_getD, hv']
  have htBorder : proxy.node.border = -2 ∨ proxy.node.border = 2 := by
    right
    rw [← htGetD]; exact htborder
  have hdummy' : other.dummy = true := by rw [← hvGetD]; exact hdummy
  obtain ⟨_rr, _labeled, _hrr, hcoord, hkeys, _, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  have hborderV : other.node.border = 0 :=
    pc_plain hkeys (by rw [hcoord]; exact hv') hdummy'
  have hvNotProxy : ¬(other.node.border = -2 ∨ other.node.border = 2) := by
    rw [hborderV]; decide
  have hside := sidePathEq_of_measuredGraph hgraph
  obtain ⟨owner, leftIndex, rightIndex, left, right, ownerEq, hleft, hright,
    _hleftProper, _hrightProper, hleftBorder, hrightBorder, hleftOwner, hrightOwner,
    hleftRank, hrightRank, hleftEq, hrightEq⟩ :=
    componentRun_proxy_border_extrema hrun ht' htBorder
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with hb | hb <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with hb | hb <;> omega
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hlayTV : OrderImpl.lay run.coordinateProper t =
      OrderImpl.lay run.coordinateProper v := by
    unfold OrderImpl.lay
    rw [hrankEq]
  obtain ⟨_, hvIn0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hv'
  rw [← hlayTV] at hvIn0
  have hlayLen : OrderImpl.lay run.coordinateProper t < run.layers.length := by
    rw [← hlayers]
    exact (ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord
      horder ht').1
  let layer : List Nat := run.layers[OrderImpl.lay run.coordinateProper t]'hlayLen
  have hlayerMem : layer ∈ run.layers := List.getElem_mem hlayLen
  have hopt : run.layers[OrderImpl.lay run.coordinateProper t]? = some layer :=
    List.getElem?_eq_some_iff.mpr ⟨hlayLen, rfl⟩
  have hvMemL : v ∈ layer := by
    have h1 := hvIn0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hlayL : OrderImpl.lay run.coordinateProper leftIndex =
      OrderImpl.lay run.coordinateProper t := by
    unfold OrderImpl.lay
    rw [hleftRank]
  have hlayR : OrderImpl.lay run.coordinateProper rightIndex =
      OrderImpl.lay run.coordinateProper t := by
    unfold OrderImpl.lay
    rw [hrightRank]
  obtain ⟨_, hleftMemOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hleft
  obtain ⟨_, hrightMemOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hright
  rw [hlayL] at hleftMemOrd
  rw [hlayR] at hrightMemOrd
  have hleftMem : leftIndex ∈ layer := by
    have h1 := hleftMemOrd
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hrightMem : rightIndex ∈ layer := by
    have h1 := hrightMemOrd
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  obtain ⟨leftPos, hleftPos⟩ := List.mem_iff_getElem?.mp hleftMem
  obtain ⟨rightPos, hrightPos⟩ := List.mem_iff_getElem?.mp hrightMem
  obtain ⟨vPos, hvPos⟩ := List.mem_iff_getElem?.mp hvMemL
  have hleftGD : run.coordinateProper.nodes.getD leftIndex default = left := by
    simp [List.getD_eq_getElem?_getD, hleft]
  have hrightGD : run.coordinateProper.nodes.getD rightIndex default = right := by
    simp [List.getD_eq_getElem?_getD, hright]
  obtain ⟨hleftPath, hleftDummy⟩ := hside comp hcomp candidate run labels
    orderOptions hrun t leftIndex htborder
    (by rw [hleftGD]; exact hleftBorder) (by rw [htGetD, hleftGD]; exact ownerEq.trans hleftOwner.symm)
  obtain ⟨hrightPath, hrightDummy⟩ := hside comp hcomp candidate run labels
    orderOptions hrun t rightIndex htborder
    (by rw [hrightGD]; exact hrightBorder) (by rw [htGetD, hrightGD]; exact ownerEq.trans hrightOwner.symm)
  rcases Nat.lt_trichotomy vPos leftPos with hvl | hvl | hvl
  · have hsepL : RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
        RouteImpl.leftOf run.proper run.xs leftIndex :=
      componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem hvl
        hvPos hleftPos hv' hleft hvNotProxy hleftNotProxy
    rw [← hleftEq] at hsepL
    exact Or.inr hsepL
  · exfalso
    have hvEqL : v = leftIndex := by
      rw [hvl] at hvPos
      rw [hleftPos] at hvPos
      exact Option.some.inj hvPos.symm
    subst hvEqL
    have heqL : other = left := Option.some.inj (hv'.symm.trans hleft)
    have hleftFalse : left.dummy = false := by
      rw [← hleftGD]; exact hleftDummy
    rw [heqL] at hdummy'
    rw [hleftFalse] at hdummy'
    exact absurd hdummy' (by decide)
  · rcases Nat.lt_trichotomy vPos rightPos with hvr | hvr | hvr
    · have hpref : (run.coordinateProper.nodes.getD t default).node.clusterPath <+:
          OrderImpl.nodePath run.coordinateProper v := by
        have hpre : (run.coordinateProper.nodes.getD leftIndex default).node.clusterPath <+:
            OrderImpl.nodePath run.coordinateProper v := by
          apply dummy_interior_prefix hgraph hcomp hrun hlayerMem hleftPos hvPos hrightPos
            hvl hvr
          · rw [hleftGD]; exact hleftBorder
          · rfl
          · rw [hrightGD]; exact hrightBorder
          · exact hrightPath.trans hleftPath.symm
        have hEq : (run.coordinateProper.nodes.getD leftIndex default).node.clusterPath =
            (run.coordinateProper.nodes.getD t default).node.clusterPath :=
          hleftPath
        rw [hEq] at hpre
        exact hpre
      have hne := hRank comp hcomp candidate run labels orderOptions hrun t v
        htborder hdummy hpref
      exfalso
      exact hne hrankEq
    · exfalso
      have hvEqR : v = rightIndex := by
        rw [hvr] at hvPos
        rw [hrightPos] at hvPos
        exact Option.some.inj hvPos.symm
      subst hvEqR
      have heqR : other = right := Option.some.inj (hv'.symm.trans hright)
      have hrightFalse : right.dummy = false := by
        rw [← hrightGD]; exact hrightDummy
      rw [heqR] at hdummy'
      rw [hrightFalse] at hdummy'
      exact absurd hdummy' (by decide)
    · have hsepR : RouteImpl.leftOf run.proper run.xs rightIndex +
          RouteImpl.nodeW run.proper rightIndex ≤
          RouteImpl.leftOf run.proper run.xs v :=
        componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem hvr
          hrightPos hvPos hright hv' hrightNotProxy hvNotProxy
      rw [← hrightEq] at hsepR
      exact Or.inl hsepR
 /-- `boxLines` produces one line block per input box. -/
 private theorem dummy_lines_length {m : Measure.Metric} {target : Int}
     {inp : Input} {lines : List (List Measure.Line)}
     (h : boxLines m target inp = .ok lines) : lines.length = inp.boxes.length := by
   unfold boxLines at h
   have hlen := (mapM_getElem? _ _ _ h).1
   have hzip : (inp.boxes.zipIdx).length = inp.boxes.length := List.length_zipIdx
   omega

 /-- A list's last element is a member. -/
 private theorem mem_of_getLast?_eq_some_dm {l : List Nat} {a : Nat}
     (h : l.getLast? = some a) : a ∈ l := by
   induction l with
   | nil => exact absurd h (by simp)
   | cons x xs ih =>
       rw [List.getLast?_cons] at h
       have hinj : xs.getLast?.getD x = a := Option.some.inj h
       cases hgl : xs.getLast? with
       | none =>
           rw [hgl, Option.getD_none] at hinj
           rw [← hinj]
           exact List.mem_cons_self ..
       | some z =>
           rw [hgl, Option.getD_some] at hinj
           have hih : xs.getLast? = some a := by rw [hgl, hinj]
           exact List.mem_cons_of_mem x (ih hih)

 /-- Run-to-labeled lookup at an original index forces the real case. -/
 private theorem coordinate_lookup_original {P : Params} {p : Proper} {v : Nat} {nd : ProperNode}
     (h : (coordinateGraph P p).nodes[v]? = some nd)
     (hlt : v < p.nodes.length) :
     ∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border := by
   have hspLen : (sizeProperPorts P p).nodes.length = p.nodes.length := sizeProperPorts_length P p
   have hmat : ∃ m1, (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[v]? = some m1 ∧
       nd.dummy = m1.dummy ∧ nd.node.border = m1.node.border := by
     have h' : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPorts P p)) P.clusterBorderW))).nodes[v]? = some nd := h
     obtain ⟨m1, hm1, hd, hb, _, _⟩ := materialize_lookup _ h'
     exact ⟨m1, hm1, hd, hb⟩
   obtain ⟨m1, hm1, hdM, hbM⟩ := hmat
   have htitleLen : (sizeProperPorts P p).nodes.length ≤
       (titleReservations (sizeProperPorts P p)).nodes.length := by
     rw [titleReservations_nodes]
     simp only [List.length_map, List.length_append]
     omega
   obtain ⟨_, hx, _⟩ := addClusterBorders_extra
     (titleReservations (sizeProperPorts P p)) P.clusterBorderW
   have hvTitled : v < (titleReservations (sizeProperPorts P p)).nodes.length := by omega
   have hvSized : v < (sizeProperPorts P p).nodes.length := by omega
   rw [clearProxyExtents_nodes] at hm1
   simp only [List.getElem?_map] at hm1
   obtain ⟨m2, hm2get, hm2eq⟩ : ∃ m2, (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[v]? = some m2 ∧
       clearF m2 = m1 := by
     cases h2 : (OrderImpl.addClusterBorders (titleReservations (sizeProperPorts P p))
         P.clusterBorderW).nodes[v]? with
     | none => simp [h2] at hm1
     | some m2 =>
         simp only [h2, Option.map_some, Option.some.injEq] at hm1
         exact ⟨m2, rfl, hm1⟩
   obtain ⟨c1, c2, _, _⟩ := clearF_keys m2
   rw [hx] at hm2get
   rw [List.getElem?_append_left hvTitled] at hm2get
   rw [titleReservations_nodes] at hm2get
   have hmapLen : ((sizeProperPorts P p).nodes.map titleF).length =
       (sizeProperPorts P p).nodes.length := by simp
   have hvMap : v < ((sizeProperPorts P p).nodes.map titleF).length := by omega
   rw [List.getElem?_append_left hvMap] at hm2get
   simp only [List.getElem?_map] at hm2get
   obtain ⟨s, hsget, hts⟩ : ∃ s, (sizeProperPorts P p).nodes[v]? = some s ∧ titleF s = m2 := by
     cases hs : (sizeProperPorts P p).nodes[v]? with
     | none => simp [hs] at hm2get
     | some s =>
       simp only [hs, Option.map_some, Option.some.injEq] at hm2get
       exact ⟨s, rfl, hm2get⟩
   obtain ⟨t1, t2, _, _⟩ := titleF_keys s
   have hk := sizeProperPorts_key P p v
   rw [hsget] at hk
   cases hp : p.nodes[v]? with
   | none => simp [hp] at hk
   | some mp =>
       simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
       obtain ⟨hd, hb, _⟩ := hk
       have hdm : nd.dummy = mp.dummy := by rw [hdM, ← hm2eq, c1, ← hts, t1, hd]
       have hbdr : nd.node.border = mp.node.border := by rw [hbM, ← hm2eq, c2, ← hts, t2, hb]
       exact ⟨mp, rfl, hdm, hbdr⟩

 /-- Rank-level residual for the dummy-row seam: a marker (top or bottom
 proxy) whose cluster path contains the proxy owner's declaration ranks
 strictly below that proxy, unless it is the proxy itself. True for executed
 layouts: a same-group top sits strictly below its own bottom
 (`componentRun_group_top_lt_bottom`); a nested marker sits below its own
 bottom, which sits strictly below the outer bottom (iterate
 `componentRun_nested_bottom_lt_outer_bottom` along the declaration path);
 a distinct bottom with the same declaration is impossible
 (`measuredGraph_bottom_pair_eq`). Rank-only, hence strictly simpler than
 `dummyInsideProxyRowClear`; every variable it constrains is pinned by
 `comp ∈ components` plus the executed `componentRun`. -/
 def DummyNestedMarkerBelow (P : Params) (graph : Graph) : Prop :=
   ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
     ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
       componentRun P (componentCandidate graph comp candidate) labels orderOptions =
         .ok run →
     ∀ t b owner : Nat,
       (run.coordinateProper.nodes.getD t default).node.border = 2 →
       (run.coordinateProper.nodes.getD t default).node.clusterPath.getLast? = some owner →
       ((run.coordinateProper.nodes.getD b default).node.border = -2 ∨
         (run.coordinateProper.nodes.getD b default).node.border = 2) →
       owner ∈ (run.coordinateProper.nodes.getD b default).node.clusterPath →
       rk run.coordinateProper.rank b < rk run.coordinateProper.rank t ∨ b = t

 /-- The dummy-row rank fact holds for every executed layout, modulo the
 marker residual. A dummy whose node path extends a bottom proxy's path lies
 on its edge chain strictly between its endpoints
 (`componentRun_labeled_chain_rank_positions`); the head endpoint contains the
 proxy's owner (`commonPath_member_both`) and is either a plain member
 (strictly below the proxy by `plainMemberRankLtProxy_of_measuredGraph`) or a
 marker (strictly below the proxy, or equal to it, by the residual). Either
 way the dummy cannot share the proxy's rank: strictly below the head gives
 `rk v < rk t`; equal to the head contradicts the strict chain position. -/
 theorem dummyNestedRank {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hmark : DummyNestedMarkerBelow execution.params execution.graph) :
     DummyNestedRank execution.params execution.graph := by
   intro comp hcomp candidate run labels orderOptions hrun t v htborder hdummy hpref
   have hgraph : measuredGraph execution.params inp o execution.lines = .ok execution.graph :=
     execution.graph_eq
   have hlines : execution.lines.length = inp.boxes.length :=
     dummy_lines_length execution.lines_eq
   obtain ⟨pt, htp⟩ : ∃ x, run.coordinateProper.nodes[t]? = some x := by
     cases hx : run.coordinateProper.nodes[t]? with
     | none =>
         rw [List.getD_eq_getElem?_getD, hx, Option.getD_none] at htborder
         have hd0 : (default : ProperNode).node.border = 0 := rfl
         omega
     | some x => exact ⟨x, rfl⟩
   obtain ⟨nd, hv0⟩ : ∃ x, run.coordinateProper.nodes[v]? = some x := by
     cases hx : run.coordinateProper.nodes[v]? with
     | none =>
         rw [List.getD_eq_getElem?_getD, hx, Option.getD_none] at hdummy
         have hd0 : (default : ProperNode).dummy = false := rfl
         rw [hd0] at hdummy
         exact absurd hdummy (by decide)
     | some x => exact ⟨x, rfl⟩
   have htGetD : run.coordinateProper.nodes.getD t default = pt := by
     simp [List.getD_eq_getElem?_getD, htp]
   have hvGetD : run.coordinateProper.nodes.getD v default = nd := by
     simp [List.getD_eq_getElem?_getD, hv0]
   rw [htGetD] at htborder hpref
   rw [hvGetD] at hdummy
   have htBorder : pt.node.border = -2 ∨ pt.node.border = 2 := Or.inr htborder
   have hdummy' : nd.dummy = true := hdummy
   obtain ⟨owner, _, _, _, _, ownerEq, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
     componentRun_proxy_border_extrema hrun htp htBorder
   have hownerLast : pt.node.clusterPath.getLast? = some owner := ownerEq
   have hownerPref : owner ∈ pt.node.clusterPath :=
     mem_of_getLast?_eq_some_dm hownerLast
   have hownerPath : owner ∈ OrderImpl.nodePath run.coordinateProper v :=
     List.IsPrefix.mem hownerPref hpref
   have hnpEq : OrderImpl.nodePath run.coordinateProper v =
       match run.coordinateProper.chains.find? (fun chain => chain.contains v) with
       | none => []
       | some chain =>
           OrderImpl.commonPath ((run.coordinateProper.nodes.getD (chain.headD v) default).node.clusterPath)
             ((run.coordinateProper.nodes.getD (chain.getLastD v) default).node.clusterPath) := by
     unfold OrderImpl.nodePath
     dsimp only
     rw [hvGetD, hdummy']
     rfl
   rw [hnpEq] at hownerPath
   cases hfind : run.coordinateProper.chains.find? (fun chain => chain.contains v) with
   | none =>
       rw [hfind] at hownerPath
       dsimp only at hownerPath
       exact absurd hownerPath (by simp)
   | some chain =>
       rw [hfind] at hownerPath
       dsimp only at hownerPath
       obtain ⟨_, hownerR⟩ := commonPath_member_both _ _ hownerPath
       have hmem : v ∈ chain := by
         have hfv := List.find?_some hfind
         simpa only [List.contains_iff_mem] using hfv
       obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoord, hpositions⟩ :=
         componentRun_labeled_chain_rank_positions hrun
       have hchainsEq : run.coordinateProper.chains = labeled.chains := by
         rw [← hcoord]; exact coordinateGraph_chains execution.params _
       have hfindL : labeled.chains.find? (fun chain => chain.contains v) = some chain := by
         rw [← hchainsEq]; exact hfind
       have hchainLmem : chain ∈ labeled.chains := List.mem_of_find?_eq_some hfindL
       have hchainNmem : chain ∈ normalized.chains := by
         rw [← (Labels.addLabelNodes_metadata hlabels).2.2.1]; exact hchainLmem
       obtain ⟨index, hchainIdx⟩ := List.mem_iff_getElem?.mp hchainNmem
       have hnormLen : normalized.chains.length = (componentCandidate execution.graph comp candidate).edges.length :=
         normalize_chains_length hnormalize
       have hindex : index < (componentCandidate execution.graph comp candidate).edges.length := by
         rw [← hnormLen]; exact (List.getElem?_eq_some_iff.mp hchainIdx).1
       obtain ⟨edge, hedge⟩ : ∃ e, (componentCandidate execution.graph comp candidate).edges[index]? = some e :=
         ⟨_, List.getElem?_eq_getElem hindex⟩
       have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
       have hwf : (componentCandidate execution.graph comp candidate).wellformed = true :=
         (normalize_node_rank_alignment hnormalize).2
       have hedgeMem : edge ∈ (componentCandidate execution.graph comp candidate).edges :=
         List.mem_of_getElem? hedge
       obtain ⟨_, hhB, _⟩ := RankImpl.wellformed_spec hwf edge hedgeMem
       obtain ⟨nHead, hnHead⟩ : ∃ n, (componentCandidate execution.graph comp candidate).nodes[edge.head]? = some n :=
         ⟨_, List.getElem?_eq_getElem hhB⟩
       have hrecH : labeled.nodes[edge.head]? = some ⟨nHead, false, none, false⟩ :=
         addLabelNodes_untouched_node hlabels (normalize_node_record hnormalize hnHead) rfl
       have hcoordV0 : (coordinateGraph execution.params labeled).nodes[v]? = some nd := by
         rw [hcoord]; exact hv0
       obtain ⟨mV, hmvV, hdmV⟩ : ∃ m, labeled.nodes[v]? = some m ∧ m.dummy = true := by
         rcases coordinateGraph_lookup execution.params labeled hcoordV0 with
           ⟨m, hm, h1, _, _, _⟩ | ⟨h1, _⟩ | ⟨i, q, hq, _, h1, _, _⟩
         · exact ⟨m, hm, h1.symm.trans hdummy'⟩
         · rw [h1] at hdummy'; exact absurd hdummy' (by decide)
         · have hkeys : NodeKeys (componentCandidate execution.graph comp candidate) labeled :=
             addLabelNodes_keys _ _ _ (normalize_keys hnormalize) hlabels
           obtain ⟨hs, hbq⟩ := titleNodes_spec hq
           have hk := sizeProperPorts_key execution.params labeled q.2
           rw [hs] at hk
           cases hp : labeled.nodes[q.2]? with
           | none => simp [hp] at hk
           | some mp =>
               simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
               obtain ⟨hk1, hk2, _⟩ := hk
               rcases hkeys q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
               · rw [h1, hk1, hmd] at hdummy'
                 exact absurd hdummy' (by decide)
               · rw [hk2] at hbq
                 rw [hb'] at hbq
                 exact absurd hbq (by decide)
       have haligned : labeled.nodes.length = labeled.rank.length := by
         have h1 := addLabelNodes_node_length hlabels
         have h2 := congrArg List.length (Labels.addLabelNodes_metadata hlabels).2.1
         have h3 := (normalize_node_rank_alignment hnormalize).1
         omega
       have hvLtLab : v < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hmvV).1
       have hvrLen : v < labeled.rank.length := by rw [← haligned]; exact hvLtLab
       have hlabV : labeled.rank[v]? = some (labeled.rank[v]'hvrLen) := List.getElem?_eq_getElem hvrLen
       have hcoordV : run.coordinateProper.rank[v]? = some (labeled.rank[v]'hvrLen) := by
         rw [← hcoord]
         exact coordinateGraph_rank_record hlabV
       have hrkV : rk run.coordinateProper.rank v = rk labeled.rank v := by
         unfold rk
         rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hcoordV, hlabV]
       have hchainFacts : edge.tail ≠ edge.head ∧ chain.getLast? = some edge.head := by
         have hfact2 := hfact.2
         by_cases hself : edge.tail = edge.head
         · have hch : normalized.chains[index]? = some [] := by
             simp only [hself, ↓reduceIte] at hfact2
             exact hfact2
           have hempty : chain = [] := Option.some.inj (hchainIdx.symm.trans hch)
           rw [hempty] at hmem
           exact absurd hmem (by simp)
         · obtain ⟨actual, hactual, _, _, hlast0, _⟩ := by
             simpa only [hself, ↓reduceIte] using hfact.2
           have hactualEq : chain = actual := Option.some.inj (hchainIdx.symm.trans hactual)
           exact ⟨hself, by rw [hactualEq]; exact hlast0⟩
       obtain ⟨_, hlast⟩ := hchainFacts
       have hlastElem : chain[chain.length - 1]? = some edge.head := by
         rw [← List.getLast?_eq_getElem?]; exact hlast
       have hlastLt : chain.length - 1 < chain.length :=
         (List.getElem?_eq_some_iff.mp hlastElem).1
       obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hmem
       have hposBound : position < chain.length := (List.getElem?_eq_some_iff.mp hposition).1
       have hposNe : position ≠ chain.length - 1 := by
         intro heq
         have hveq : v = edge.head := by
           have h1 : chain[position]? = some v := hposition
           rw [heq] at h1
           exact Option.some.inj (h1.symm.trans hlastElem)
         have hmeq : mV = ⟨nHead, false, none, false⟩ := by
           have h1 : labeled.nodes[v]? = some mV := hmvV
           rw [hveq] at h1
           exact Option.some.inj (h1.symm.trans hrecH)
         rw [hmeq] at hdmV
         exact Bool.false_ne_true hdmV
       have hposLt : position < chain.length - 1 := by omega
       have hpositionValue : chain[position]'hposBound = v :=
         Option.some.inj ((List.getElem?_eq_getElem hposBound).symm.trans hposition)
       have hlastValue : chain[chain.length - 1]'hlastLt = edge.head :=
         Option.some.inj ((List.getElem?_eq_getElem hlastLt).symm.trans hlastElem)
       have hchainL : labeled.chains[index]? = some chain := by
         rw [(Labels.addLabelNodes_metadata hlabels).2.2.1]; exact hchainIdx
       have hposBase := hpositions index edge chain hedge hchainL position hposBound
       have hlastBase := hpositions index edge chain hedge hchainL (chain.length - 1) hlastLt
       have hrankV : rk labeled.rank v = rk labeled.rank edge.tail + (position : Int) := by
         rw [← hpositionValue]; exact hposBase
       have hrankH : rk labeled.rank edge.head = rk labeled.rank edge.tail + ((chain.length - 1 : Nat) : Int) := by
         rw [← hlastValue]; exact hlastBase
       have hgd : chain.getLastD v = edge.head := by
         rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
       have hownerRhead : owner ∈ (run.coordinateProper.nodes.getD edge.head default).node.clusterPath := by
         rw [← hgd]; exact hownerR
       obtain ⟨ndH, hhvH⟩ : ∃ ndh, run.coordinateProper.nodes[edge.head]? = some ndh := by
         cases hr : run.coordinateProper.nodes[edge.head]? with
         | none =>
             exfalso
             have hget : run.coordinateProper.nodes.getD edge.head default = default := by
               simp [List.getD_eq_getElem?_getD, hr]
             rw [hget] at hownerRhead
             have hnil : (default : ProperNode).node.clusterPath = [] := rfl
             rw [hnil] at hownerRhead
             exact absurd hownerRhead (by simp)
         | some ndh => exact ⟨_, rfl⟩
       have hheadLtLab : edge.head < labeled.nodes.length := by
         have h1 : edge.head < (componentCandidate execution.graph comp candidate).nodes.length := hhB
         have h2 : (componentCandidate execution.graph comp candidate).nodes.length ≤ normalized.nodes.length :=
           normalize_nodes_length_le hnormalize
         have h3 : normalized.nodes.length = labeled.nodes.length := addLabelNodes_node_length hlabels
         omega
       have hhvH' : (coordinateGraph execution.params labeled).nodes[edge.head]? = some ndH := by
         rw [hcoord]; exact hhvH
       obtain ⟨mH, hmH, hdH, hbH⟩ := coordinate_lookup_original hhvH' hheadLtLab
       have hmeqH : mH = ⟨nHead, false, none, false⟩ :=
         Option.some.inj (hmH.symm.trans hrecH)
       have hdHfalse : ndH.dummy = false := by rw [hdH, hmeqH]
       have hbHrun : ndH.node.border = nHead.border := by rw [hbH, hmeqH]
       have hgetDhead : run.coordinateProper.nodes.getD edge.head default = ndH := by
         simp [List.getD_eq_getElem?_getD, hhvH]
       have hshapeH := componentCandidate_marker_shape hgraph hnHead
       have hheadLen : edge.head < labeled.rank.length := by rw [← haligned]; exact hheadLtLab
       have hlabH : labeled.rank[edge.head]? = some (labeled.rank[edge.head]'hheadLen) := List.getElem?_eq_getElem hheadLen
       have hcoordH : run.coordinateProper.rank[edge.head]? = some (labeled.rank[edge.head]'hheadLen) := by
         rw [← hcoord]
         exact coordinateGraph_rank_record hlabH
       have hrkH : rk run.coordinateProper.rank edge.head = rk labeled.rank edge.head := by
         unfold rk
         rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hcoordH, hlabH]
       have hltV : rk run.coordinateProper.rank v < rk run.coordinateProper.rank edge.head := by omega
       rcases hshapeH.1 with hbor0 | hbor2 | hbor2
       · have hcontH : ((run.coordinateProper.nodes.getD edge.head default).node.clusterPath.contains owner = true) := by
           simpa using hownerRhead
         have hheadLt : rk run.coordinateProper.rank edge.head < rk run.coordinateProper.rank t :=
           (plainMemberRankLtProxy_of_measuredGraph hgraph hlines) comp hcomp candidate run labels orderOptions hrun t edge.head
             (by rw [htGetD]; exact htborder)
             (by rw [hgetDhead]; exact hdHfalse)
             (by rw [hgetDhead, hbHrun]; exact hbor0)
             owner (by rw [htGetD]; exact hownerLast) hcontH
         omega
       · have hbHdisj : (run.coordinateProper.nodes.getD edge.head default).node.border = -2 ∨
             (run.coordinateProper.nodes.getD edge.head default).node.border = 2 := by
           rw [hgetDhead, hbHrun]; exact Or.inl hbor2
         have hres := hmark comp hcomp candidate run labels orderOptions hrun t edge.head owner
           (by rw [htGetD]; exact htborder) (by rw [htGetD]; exact hownerLast) hbHdisj hownerRhead
         rcases hres with hltH | heqH
         · omega
         · rw [heqH] at hltV
           omega
       · have hbHdisj : (run.coordinateProper.nodes.getD edge.head default).node.border = -2 ∨
             (run.coordinateProper.nodes.getD edge.head default).node.border = 2 := by
           rw [hgetDhead, hbHrun]; exact Or.inr hbor2
         have hres := hmark comp hcomp candidate run labels orderOptions hrun t edge.head owner
           (by rw [htGetD]; exact htborder) (by rw [htGetD]; exact hownerLast) hbHdisj hownerRhead
         rcases hres with hltH | heqH
         · omega
         · rw [heqH] at hltV
           omega

 /-- The dummy-row clearance seam holds for every executed layout, modulo the
 marker residual. The rank half is `dummyNestedRank`; the geometric half is
 the accepted reduction. -/
 theorem dummyInsideProxyRowClear_executed {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hmark : DummyNestedMarkerBelow execution.params execution.graph) :
     dummyInsideProxyRowClear execution.params execution.graph :=
   dummyInsideProxyRowClear_of_execution execution (dummyNestedRank execution hmark)

end Elegant.Layered.PipelineImpl
