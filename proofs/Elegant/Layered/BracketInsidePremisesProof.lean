import Elegant.Layered.FrameClearanceSeam

set_option autoImplicit false

/-!
# The three open premises of the bracket-inside seam

`BracketInsidePremises` (`FrameClearanceSeam.lean`) bundles the three clauses
`bracket_inside_rank_below_bottom` still takes, per executed flat layout:

1. `dummyInsideProxyRowClear` — a positive-height dummy sharing a bottom
   proxy's rank keeps its x-span disjoint from the proxy span.
2. `titleCopySpanClearStrict` — the same for a border-`3` title copy.
3. `insidePrefixHypothesis` — inside the bracket of a group, every non-dummy
   layer node between the group's `±1` borders has the group's cluster path as
   a prefix of its node path.

This module discharges the third clause outright
(`componentRun_inside_prefix`): the ordered layers produced by
`orderWithBudget` keep every `pref`-prefixed node path contiguous
(`OrderImpl.order_clusters_contiguous`), the two borders of the bracket both
carry `clusterPath = pref` and are non-dummy, so any non-dummy node strictly
between them in the layer belongs to the `pref`-prefixed infix, which is
exactly `pref <+: nodePath`.  Nodup of the layer (from `Layering` via
`orderWithBudget_spec`) makes the three infix segments value-disjoint, which
is what `mem_of_between_infix` needs.

The two span clauses remain named hypotheses of `bracketInsidePremises`: each
is a statement about executed x-coordinates (`RouteImpl.leftOf`/`nodeW`), not
a repackaging of the goal — the prefix conjunct is proved here from the
executed order record alone.
-/

namespace Elegant.Layered.PipelineImpl

/-- An element strictly between two members of an infix `S` of a nodup list
`l` is itself a member of `S`: the infix is one contiguous block
`s ++ S ++ t`, nodup makes the three segments value-disjoint, and the
positional bounds force the middle index into the `S` segment. -/
theorem mem_of_between_infix {α : Type} {l S : List α} {a b c : α}
    {li vi ri : Nat}
    (hnd : l.Nodup) (h : S.IsInfix l)
    (ha : a ∈ S) (hb : b ∈ S)
    (hli : l[li]? = some a) (hvi : l[vi]? = some c) (hri : l[ri]? = some b)
    (hlt : li < vi) (hgt : vi < ri) : c ∈ S := by
  obtain ⟨s, t, hs⟩ := h
  subst hs
  -- `l = (s ++ S) ++ t`; nodup makes the three segments pairwise disjoint.
  have hnd' := List.nodup_append.mp hnd
  have hsS : ∀ x ∈ s, ∀ y ∈ S, x ≠ y :=
    (List.nodup_append.mp hnd'.1).2.2
  have hSt : ∀ x ∈ s ++ S, ∀ y ∈ t, x ≠ y := hnd'.2.2
  have hlen : (s ++ S).length = s.length + S.length := List.length_append ..
  -- `li` lies in the `S` segment: `li ≥ s.length` since `a ∈ S` and `a ∉ s`.
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
  -- `ri` lies in the `S` segment.
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
  -- `vi` lies in the `S` segment by squeeze.
  have hviS : s.length ≤ vi ∧ vi < (s ++ S).length := by
    constructor <;> omega
  -- `v`'s flat index inside `S` is `vi - s.length`.
  have hlook : ((s ++ S) ++ t)[vi]? = S[vi - s.length]? := by
    rw [List.getElem?_append_left hviS.2,
      List.getElem?_append_right (by omega : s.length ≤ vi)]
  rw [hlook] at hvi
  exact List.mem_of_getElem? hvi

/-- The inside-prefix hypothesis holds for every successful component run:
non-dummy layer nodes strictly between two `±1` borders that share the cluster
path `pref` have `pref` as a prefix of their node path.  Proof: the ordered
layers keep the `pref`-prefixed node paths contiguous
(`order_clusters_contiguous`), both borders lie in that infix (their node path
is their cluster path `pref`), and `v` sits strictly between them, so `v` is in
the infix; `v` non-dummy turns `isPrefixOf` into `IsPrefix` on `nodePath`. -/
theorem componentRun_inside_prefix {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∀ pref : List Nat, insidePrefixHypothesis run orderOptions pref := by
  intro pref
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _⟩ :=
    componentRun_spec hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions =
      .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  refine ⟨hwf, ?_⟩
  intro layer hlayer li vpos ri l r v
    hl hv hr hlr hvl hvr hlb hrb hlp hrp hld hrd
  have hinfix := OrderImpl.order_clusters_contiguous run.coordinateProper
    orderOptions run.layers horder' layer hlayer pref
  -- Node path of a non-dummy `±1` border equals its cluster path.
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
  -- `l` and `r` lie in the `pref`-prefixed infix.
  have hlS : l ∈ layer.filter (fun x =>
      pref.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_of_getElem? hl, ?_⟩
    cases hxl : run.coordinateProper.nodes[l]? with
    | none =>
        have hxlD : run.coordinateProper.nodes.getD l default = default := by
          simp [List.getD_eq_getElem?_getD, hxl]
        rw [hxlD] at hvr
        have hd0 : (default : ProperNode).node.border = 0 := rfl
        omega
    | some nl =>
        have hxlD : run.coordinateProper.nodes.getD l default = nl := by
          simp [List.getD_eq_getElem?_getD, hxl]
        have hlb' : nl.node.border = -1 ∨ nl.node.border = 1 := by
          rw [← hxlD]; exact hvr
        have hlp' : nl.node.clusterPath = pref := by
          rw [← hxlD]; exact hlb
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
        rw [hxrD] at hlp
        have hd0 : (default : ProperNode).node.border = 0 := rfl
        omega
    | some nr =>
        have hxrD : run.coordinateProper.nodes.getD r default = nr := by
          simp [List.getD_eq_getElem?_getD, hxr]
        have hrb' : nr.node.border = -1 ∨ nr.node.border = 1 := by
          rw [← hxrD]; exact hlp
        have hrp' : nr.node.clusterPath = pref := by
          rw [← hxrD]; exact hrp
        have hnp := hnpBorder r nr hxr hrb' hrp'
        rw [hnp]
        exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  -- Nodup of the layer (from `Layering` via `orderWithBudget_spec`).
  have hLspec := OrderImpl.orderWithBudget_spec run.coordinateProper
    orderOptions ord horder
  obtain ⟨k, hk, hkl⟩ := List.mem_iff_getElem.mp hlayer
  have hk2 : k < ord.layers.length := by rw [hlayers]; exact hk
  have hndlayer : layer.Nodup := by
    have h := OrderImpl.layer_nodup hLspec.1 hk2
    rw [hlayers] at h
    rw [← hkl, @List.getElem_eq_getD (List Nat) run.layers k hk []]
    exact h
  -- `v` sits strictly between the borders, hence inside the infix.
  have hvS : v ∈ layer.filter (fun x =>
      pref.isPrefixOf (OrderImpl.nodePath run.coordinateProper x)) := by
    have hmem := mem_of_between_infix hndlayer hinfix hlS hrS hl hv hr
      hlr hvl
    exact hmem
  rw [List.mem_filter] at hvS
  exact List.isPrefixOf_iff_prefix.mp hvS.2

/-- `BracketInsidePremises` holds once the two executed x-span clauses are
supplied: the prefix conjunct is proved for every executed component run by
`componentRun_inside_prefix`, and the two span clauses are exactly the
remaining named premises. -/
theorem bracketInsidePremises {inp : Input} {o : Options} {res : FamilyResult}
    (hdummy : ∀ execution : SceneExecution inp o res,
      dummyInsideProxyRowClear execution.params execution.graph)
    (htitle : ∀ execution : SceneExecution inp o res,
      titleCopySpanClearStrict execution.params execution.graph) :
    BracketInsidePremises inp o res := by
  intro execution
  refine ⟨hdummy execution, htitle execution, ?_⟩
  intro comp hcomp candidate run labels orderOptions hrun pref
  exact componentRun_inside_prefix execution.graph_eq hcomp hrun pref

end Elegant.Layered.PipelineImpl
