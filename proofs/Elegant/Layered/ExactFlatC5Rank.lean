import Elegant.Layered.ExactFlatC5
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Compound
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.Normalize
import Elegant.Layered.Rank
import Elegant.Layered.Labels
import Elegant.Layered.Pipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact rank closure for the exact pipeline (`X_TopRank`, `X_BottomBoundary`).

Target statements (proved at the end of this file):
  `theorem x_topRank_holds (exactIds : List String) : X_TopRank exactIds`
  `theorem x_bottomBoundary_holds (exactIds : List String) : X_BottomBoundary exactIds`

Route (mirrors `GroupTopRankResidualsProof` + `DummyChainRankProof`):
  (1) `X_componentRun_ranked_source` (replay of
      `GroupWidthFacts.componentRun_ranked_source` through `componentRunX_spec`);
  (2) `X_proper_rank_eq_local`;
  (3) candidate-graph closure `X_GroupTopSubtreeRankCg` (needs `X_` versions of
      `cg_group_box`, `cg_scope_prefix`, `cg_nested_top_rank`,
      `componentRun_group_top_lt_bottom`, `componentRun_cg_bottom_find`,
      `componentRun_cg_top_of_bottom`, `componentCandidate_bottom_find_eq`;
      ranking consumes only borders, decls, paths and edges, which
      `exactGraph` preserves);
  (4) `X_properDerivedRank` (dummy, side and title rank lemmas);
  (5) seam case split.

Ranking note: `componentRunX` runs `rankWithBudget (Compound.rankingGraph cg)`
as its first step, exactly like `componentRun`; `reserveExactRanks` only
produces the `ys`/`top` coordinate lists afterwards and never touches ranks.
-/

private theorem X_bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A list prefix take is a prefix. -/
private theorem X_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

/-- A prefix is the take of its length. -/
private theorem X_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

/-- Of two prefixes of one list, the shorter is a prefix of the longer. -/
private theorem X_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := X_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact X_take_is_prefix q p.length

/-- Mutual prefixes are equal. -/
private theorem X_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := X_prefix_take_eq h1
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
private theorem X_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      X_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (X_prefix_antisymm hp h2) hne

/-- Dropping the last element is a prefix. -/
private theorem X_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

/-- A cluster path ending in `d` has last element `d`. -/
private theorem X_exactGraph_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

/-- A cluster path ending in `d` has last element `d`. -/
private theorem X_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

private theorem X_isEmpty_false_ne_nil {α : Type} {l : List α} (h : l.isEmpty = false) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

private theorem X_le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- Exact ranked source: replay of `GroupWidthFacts.componentRun_ranked_source`
through the exact run equations. Ranking is the first step of `componentRunX`,
identical to `componentRun`. -/
theorem X_componentRun_ranked_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      ∀ edge ∈ (Compound.rankingGraph cg).edges,
        edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
  unfold componentRunX at h
  obtain ⟨rr, hrr, h⟩ := X_bind_ok h
  obtain ⟨normalized, hn, h⟩ := X_bind_ok h
  obtain ⟨labeled, hl, h⟩ := X_bind_ok h
  obtain ⟨ord, _, h⟩ := X_bind_ok h
  obtain ⟨xs, _, h⟩ := X_bind_ok h
  obtain ⟨routed, _, h⟩ := X_bind_ok h
  obtain ⟨routing, _, h⟩ := X_bind_ok h
  obtain ⟨yt, _, h⟩ := X_bind_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := X_bind_ok h
  obtain ⟨routes, _, h⟩ := X_bind_ok h
  have heq := Except.ok.inj h
  subst run
  refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
  apply rank_feasible (Compound.rankingGraph cg) rr.ranks
  simp only [RankImpl.rank, hrr]

/-- Executed exact proper ranks agree with exact coordinate ranks index-wise. -/
theorem X_proper_rank_eq_local {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) (x : Nat) :
    rk run.proper.rank x = rk run.coordinateProper.rank x := by
  have h : run.proper.rank = run.coordinateProper.rank := by
    obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, _, _, _⟩ :=
      componentRunX_spec hrun
    obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hprox
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  rw [h]

/-- Exact candidate `-2` node path source in input boxes: transport across
`exactGraph` (same index, same key fields) then use the measured origin. -/
theorem X_cg_group_box {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨orig, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨nd0, hnd0, hborder0, hpath0, hdecl0⟩ := X_exactGraph_node_key_rev h hsource
  have hgroup0 : nd0.border = -2 := by rw [← hborder0]; exact hgroup
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin h0 hnd0 hgroup0
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  rw [← hdecl] at hbox
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  have hbox' : inp.boxes[node.decl]? = some box := by
    have e : node.decl = nd0.decl := hdecl0
    rw [e]; exact hbox
  have hpath' : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    have e1 : node.clusterPath = nd0.clusterPath := hpath0
    have e2 : nd0.decl = node.decl := hdecl0.symm
    rw [← hchange] at hpath
    rw [hpathMap] at hpath
    rw [e1, ← e2]
    exact hpath
  exact ⟨box, hbox', hpath'⟩

/-- Exact candidate bottom-marker path source in input boxes. -/
theorem X_cg_bottom_box {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨orig, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨nd0, hnd0, hborder0, hpath0, hdecl0⟩ := X_exactGraph_node_key_rev h hsource
  have hborder0' : nd0.border = 2 := by rw [← hborder0]; exact hborder
  obtain ⟨boxD, hboxD, hroleD, hpathD, _, _⟩ :=
    measuredGraph_bottom_origin h0 (List.mem_of_getElem? hnd0) hborder0'
  rw [List.getElem?_map] at hboxD
  obtain ⟨origBox, horig, hchange⟩ := Option.map_eq_some_iff.mp hboxD
  have hnotfixed : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == origBox.id) = true) := by
    intro hfixed
    have heq : ({ origBox with role := .node } : ModelBox) = boxD := by
      simpa [hfixed] using hchange
    rw [← heq] at hroleD
    simp at hroleD
  have hboxEq : boxD = origBox := by
    have hif : (if inp.fixedSizes.any (fun fixed => fixed.1 == origBox.id) then
        ({ origBox with role := .node } : ModelBox)
        else origBox) = origBox := ite_eq_right hnotfixed
    simpa [hif] using hchange.symm
  obtain ⟨_, _, hpathMap0⟩ := fixedSizes_path_index inp horig
  have hpathMap : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        ({ box with role := .node } : ModelBox) else box) origBox =
      Compound.path inp.boxes origBox := by
    simpa [hnotfixed] using hpathMap0
  have hbox' : inp.boxes[node.decl]? = some origBox := by
    have e : node.decl = nd0.decl := hdecl0
    rw [e]; exact horig
  have hpath' : node.clusterPath = Compound.path inp.boxes origBox ++ [node.decl] := by
    have e1 : node.clusterPath = nd0.clusterPath := hpath0
    have e2 : nd0.decl = node.decl := hdecl0.symm
    rw [← e1, hboxEq] at hpathD
    rw [hpathMap] at hpathD
    rw [hpathD, e2]
  exact ⟨origBox, hbox', hpath'⟩

/-- Scope prefix: a marker whose cluster path contains a group top's
declaration extends that top's cluster path. Graph-agnostic copy of
`cg_scope_prefix`. -/
theorem X_cg_scope_prefix {inp : Input} {o : Options}
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

/-- Same-path exact group tops share their candidate index. -/
theorem X_cg_top_unique {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbA : na.border = -2) (hbB : nb.border = -2)
    (hpath : na.clusterPath = nb.clusterPath) : a = b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := X_cg_group_box h0 h ha hbA
    exact X_cg_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := X_cg_group_box h0 h hb hbB
    exact X_cg_path_last hpathB
  have hdecl : na.decl = nb.decl := by
    have h := congrArg List.getLast? hpath
    rw [hlastA, hlastB] at h
    exact Option.some.inj h
  obtain ⟨aSrc, haSrc, hsa⟩ := componentCandidate_nonplain_source ha (by omega)
  obtain ⟨bSrc, hbSrc, hsb⟩ := componentCandidate_nonplain_source hb (by omega)
  obtain ⟨ndA, hndA, hbordA, _, hdeclA0⟩ := X_exactGraph_node_key_rev h hsa
  obtain ⟨ndB, hndB, hbordB, _, hdeclB0⟩ := X_exactGraph_node_key_rev h hsb
  have hbA0 : ndA.border = -2 := by rw [← hbordA]; exact hbA
  have hbB0 : ndB.border = -2 := by rw [← hbordB]; exact hbB
  obtain ⟨hdeclA, _, _, _, _⟩ := measuredGraph_group_origin h0 hndA hbA0
  obtain ⟨hdeclB, _, _, _, _⟩ := measuredGraph_group_origin h0 hndB hbB0
  have hsrc : aSrc = bSrc := by omega
  exact nodup_map_inj_aux (fun x => x)
    (by simpa using components_nodup graph comp hcomp) haSrc hbSrc hsrc

/-- Exact candidate marker shape: transport across `exactGraph`, then the measured fact. -/
theorem X_componentCandidate_marker_shape {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  by_cases hplain : node.border = 0
  · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
  · obtain ⟨orig, ho, hsource⟩ := componentCandidate_nonplain_source hnode hplain
    obtain ⟨nd0, hnd0, hborder0, hpath0, _⟩ := X_exactGraph_node_key_rev h hsource
    obtain ⟨hdisj, hne⟩ := measuredGraph_marker_shape h0 hnd0
    refine ⟨by simpa [hborder0] using hdisj, fun hg => ?_⟩
    have hg0 : nd0.border = -2 := by rw [← hborder0]; exact hg
    have hne0 := hne hg0
    rwa [← hpath0] at hne0

/-- Transport a key-predicate `find?` hit from the measured graph to the exact graph. -/
theorem X_find?_transport {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (pred : Node × Nat → Bool)
    (hcong : ∀ (n n0 : Node) (i : Nat), n.border = n0.border → n.decl = n0.decl →
      n.clusterPath = n0.clusterPath → pred (n, i) = pred (n0, i))
    {b : Node × Nat} (hb : b ∈ graph0.nodes.zipIdx) (hpred_b : pred b = true) :
    ∃ b' : Node × Nat, graph.nodes.zipIdx.find? pred = some b' := by
  have hlook : graph0.nodes[b.2]? = some b.1 := List.mem_zipIdx_iff_getElem?.mp hb
  obtain ⟨e, heelook, heb, hep, hed⟩ := exactGraph_node_key h hlook
  have hmem : (e, b.2) ∈ graph.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr heelook
  have hpred_e : pred (e, b.2) = true := by
    have hbe := hcong e b.1 b.2 heb hed hep
    rw [hbe]; exact hpred_b
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(e, b.2), hmem, hpred_e⟩)
  exact ⟨b', hb'⟩

/-- Exact edge/bound accounting: edges transfer, constraints are structural. -/
theorem X_exactConstraintsBounded {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length) :
    ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := by
  intro e he
  have hlen : graph.nodes.length = graph0.nodes.length := exactGraph_length h
  have hedge : graph.edges = graph0.edges := exactGraph_edges h
  rcases List.mem_append.mp he with he | he
  · rw [hedge] at he
    have hbd := measuredGraph_edges_bounded h0 hlines e he
    omega
  · exact constraints_bounded graph e he

private theorem X_findSomeOfMember {l : List (Node × Nat)} {pred : Node × Nat → Bool}
    {entry : Node × Nat} (hmem : entry ∈ l) (hp : pred entry = true) :
    ∃ b : Node × Nat, l.find? pred = some b :=
  Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨entry, hmem, hp⟩)

private theorem X_demote_length {inp : Input} :
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box).length ≤ inp.boxes.length := by
  rw [List.length_map]
  exact Nat.le_refl _

/-- Every exact-graph group top finds its paired bottom marker by declaration. -/
theorem X_groupTopFind?_some {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {t : Node × Nat} (htop : t ∈ graph.nodes.zipIdx) (hgroup : t.1.border = -2) :
    ∃ b : Node × Nat,
      graph.nodes.zipIdx.find? (fun e => e.1.border == 2 && e.1.decl == t.1.decl) = some b := by
  have hlook : graph.nodes[t.2]? = some t.1 := List.mem_zipIdx_iff_getElem?.mp htop
  obtain ⟨t0, ht0look, htbord, htpath, htdecl⟩ := X_exactGraph_node_key_rev h hlook
  have hgroup0 : t0.border = -2 := by rw [← htbord]; exact hgroup
  obtain ⟨hdecl0, box, hbox, hrole, _⟩ := measuredGraph_group_origin h0 ht0look hgroup0
  have hbound : t0.decl < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hbox).1
    rw [List.length_map] at hi
    omega
  obtain ⟨_, bottom, _, hbmem, _, hbborder, _, hbdecl, _, _, _, _⟩ :=
    measuredGraph_paired_markers h0 hbound hbox hrole
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hbmem
  have hp0 : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl)
      (bottom, idx)) = true := by
    simp [hbborder, hbdecl, ← htdecl]
  have hcong : ∀ (n n0 : Node) (i : Nat), n.border = n0.border → n.decl = n0.decl →
      n.clusterPath = n0.clusterPath →
      (fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl) (n, i) =
        (fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl) (n0, i) := by
    intro n n0 i hb hd _
    simp [hb, hd]
  have hbmem0 : (bottom, idx) ∈ graph0.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hidx
  obtain ⟨b, hb⟩ := X_find?_transport h
    (fun e : Node × Nat => e.1.border == 2 && e.1.decl == t.1.decl) hcong hbmem0 hp0
  exact ⟨b, hb⟩

/-- Exact connectivity bridge: a constraint edge keeps its head in the component. -/
private theorem X_pushIntoComp {graph : Graph} {comp : List Nat}
    (hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length)
    (hcompMem : comp ∈ components graph)
    {e : Edge} (he : e ∈ graph.edges ++ Compound.constraints graph)
    (hta : e.tail ∈ comp) : e.head ∈ comp := by
  obtain ⟨c, hcMem, hca, hcb⟩ := components_edge_endpoints hbd he
  have heq : c = comp := components_shared_member_eq hcMem hcompMem hca hta
  rw [heq] at hcb
  exact hcb

/-- Exact whole-graph marker nonemptiness via transport. -/
theorem X_graph_marker_nonempty {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {n : Node} (hmem : n ∈ graph.nodes) (hgroup : n.border = -2) :
    n.clusterPath ≠ [] := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hmem
  have hlook : graph.nodes[idx]? = some n := hidx
  obtain ⟨n0, hn0look, hnbord, hnpath, _⟩ := X_exactGraph_node_key_rev h hlook
  have hg0 : n0.border = -2 := by rw [← hnbord]; exact hgroup
  have hne := (measuredGraph_marker_shape h0 hn0look).2 hg0
  rwa [← hnpath] at hne

/-- Exact sizing preserves per-index node origin records. -/
theorem X_sizeProperPorts_node_origin (P : Params) (exact : List Nat) (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

/-- Exact title-node origin classification. Replay of `titled_node_origin`. -/
theorem X_titled_node_origin {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
    (hnode : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some node) :
    (∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath) ∨
    (node.dummy = false ∧ node.node.border = 3) := by
  rw [titleReservations_nodes] at hnode
  have hlen : (sizeProperPortsX P exact source).nodes.length = source.nodes.length := by
    simp [sizeProperPortsX]
  by_cases hi : index < (sizeProperPortsX P exact source).nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map] at hnode
    obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨original, horiginal, hd, hb, hp⟩ :=
      X_sizeProperPorts_node_origin P exact source hsized
    have ht := titleF_keys sized
    rw [heq] at ht
    exact Or.inl ⟨original, horiginal, ht.1.trans hd,
      ht.2.1.trans hb, ht.2.2.1.trans hp⟩
  · rw [List.getElem?_append_right (by
      simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getElem?_map] at hnode
    obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hd, hb, _⟩ :=
      X_sizeProperPorts_node_origin P exact source hsized
    have hreal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · rw [hplain] at hb
        omega
    right
    rw [← heq]
    exact ⟨hd.trans hreal, rfl⟩

/-- Exact title-reservation rank alignment. Replay of `titleReservations_node_rank_alignment`. -/
theorem X_titleReservations_node_rank_alignment (P : Params) {exact : List Nat} {source : Proper}
    (h : source.nodes.length = source.rank.length) :
    (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length := by
  rw [titleReservations_nodes]
  simp only [List.length_append, List.length_map, sizeProperPortsX_length]
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank]
  simp only [List.length_append, List.length_map]
  omega

/-- Exact titled border readiness. Replay of `titled_border_ready`. -/
theorem X_titled_border_ready {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, X_titleReservations_node_rank_alignment P haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases X_titled_node_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases X_titled_node_origin hkeys hb with
        ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_node_origin hkeys hindex with
      ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy

/-- Exact shared run bundle: ranking result, labeled graph, key/record transports. -/
theorem X_cg_run_bundle {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations (sizeProperPortsX P exact labeled)) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) ∧
      labeled.nodes.length = labeled.rank.length := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := X_componentRun_ranked_source hrun
  have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate
  have hready := X_titled_border_ready (P := P) (exact := exact) hk hshape
    (fun _ _ hnode => X_componentCandidate_marker_shape h0 h hnode) haligned
  refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_, haligned⟩
  · intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  · intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank

/-- Exact candidate bottom existence: every exact-graph group top in `comp` finds its
paired bottom marker in the candidate. Replay of `candidate_group_bottom_find`. -/
theorem X_candidate_group_bottom_find {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {top : Node × Nat} (hmem : top ∈ graph.nodes.zipIdx) (htopinc : top.2 ∈ comp)
    (hgroup : top.1.border = -2) :
    ∃ bottom : Node × Nat,
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom := by
  have hbd := X_exactConstraintsBounded h0 h hlines
  have key : ∀ fuel : Nat, ∀ t : Node × Nat, t ∈ graph.nodes.zipIdx →
      t.1.border = -2 →
      t.1.clusterPath.length ≤ inp.boxes.length + 1 →
      inp.boxes.length + 2 - t.1.clusterPath.length < fuel →
      ∃ gb : Node × Nat,
        graph.nodes.zipIdx.find? (fun e =>
          e.1.border == 2 && e.1.decl == t.1.decl) = some gb ∧
        ∀ c ∈ components graph, t.2 ∈ c → gb.2 ∈ c := by
    intro fuel
    induction fuel with
    | zero =>
      intro t htop hgroup _ hmeas
      exact absurd hmeas (Nat.not_lt_zero _)
    | succ fuel ih =>
      intro t htop hgroup hpathBound hmeas
      obtain ⟨gb, hfind⟩ := X_groupTopFind?_some h0 h hlines htop hgroup
      refine ⟨gb, hfind, ?_⟩
      intro c hcMem htinc
      by_cases hmemEmpty : (graph.nodes.zipIdx.filter (fun q =>
          q.1.border == 0 && q.1.clusterPath.contains t.1.decl)).isEmpty = true
      · by_cases hchildEmpty : ((graph.nodes.zipIdx.filter fun q =>
            q.1.border == -2).filter
            fun q => q.1.clusterPath.dropLast == t.1.clusterPath).isEmpty = true
        · have hdirect := compound_empty_group_constraint_edge htop hgroup hfind
            hmemEmpty hchildEmpty
          have h := X_pushIntoComp hbd hcMem (List.mem_append_right _ hdirect) htinc
          simpa using h
        · have hchildNE : ∃ child : Node × Nat,
              child ∈ ((graph.nodes.zipIdx.filter fun q => q.1.border == -2).filter
                fun q => q.1.clusterPath.dropLast == t.1.clusterPath) := by
            cases hl : ((graph.nodes.zipIdx.filter fun q => q.1.border == -2).filter
                fun q => q.1.clusterPath.dropLast == t.1.clusterPath) with
            | nil => rw [hl] at hchildEmpty; exact absurd rfl hchildEmpty
            | cons first rest => exact ⟨first, by simp⟩
          obtain ⟨child, hchild⟩ := hchildNE
          obtain ⟨hchildTops, hchildPathEq⟩ := List.mem_filter.mp hchild
          obtain ⟨hchildZip, hchildBorderBeq⟩ := List.mem_filter.mp hchildTops
          have hchildBorder : child.1.border = -2 := by simpa using hchildBorderBeq
          have hchildPath : child.1.clusterPath.dropLast = t.1.clusterPath := by
            simpa using hchildPathEq
          have hchildLookup : graph.nodes[child.2]? = some child.1 :=
            List.mem_zipIdx_iff_getElem?.mp hchildZip
          have hchildNe := X_graph_marker_nonempty h0 h
            (List.mem_of_getElem? hchildLookup) hchildBorder
          have hchildLen : child.1.clusterPath.length = t.1.clusterPath.length + 1 := by
            have h1 : child.1.clusterPath.dropLast.length =
                child.1.clusterPath.length - 1 := List.length_dropLast ..
            rw [hchildPath] at h1
            have hge : 1 ≤ child.1.clusterPath.length :=
              Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun h =>
                hchildNe (List.length_eq_zero_iff.mp h))
            have hshift : child.1.clusterPath.length - 1 + 1 =
                child.1.clusterPath.length := Nat.sub_add_cancel hge
            rw [← hshift, h1]
          have hchildPathBound : child.1.clusterPath.length ≤ inp.boxes.length + 1 := by
            have hclook : graph.nodes[child.2]? = some child.1 := hchildLookup
            obtain ⟨c0, hc0look, hcbord, hcpath, _⟩ := X_exactGraph_node_key_rev h hclook
            have hcbord0 : c0.border = -2 := by rw [← hcbord]; exact hchildBorder
            obtain ⟨_, cbox, _, _, hchildPathOrigin⟩ :=
              measuredGraph_group_origin h0 hc0look hcbord0
            have hpathLen : child.1.clusterPath.length =
                (Compound.path (inp.boxes.map fun box =>
                  if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
                    { box with role := .node } else box) cbox).length + 1 := by
              rw [hcpath, hchildPathOrigin, List.length_append, List.length_singleton]
            rw [hpathLen]
            simp only [Compound.path]
            have h := ancestors_length_le
              (inp.boxes.map fun box =>
                if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
                  { box with role := .node } else box)
              (inp.boxes.map fun box =>
                if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
                  { box with role := .node } else box).length cbox.parent
            have hdem := X_demote_length (inp := inp)
            omega
          have hchildBound : inp.boxes.length + 2 - child.1.clusterPath.length < fuel := by
            omega
          obtain ⟨cb, hcbfind, hcbprop⟩ := ih child hchildZip hchildBorder
            hchildPathBound hchildBound
          obtain ⟨he₁, he₂⟩ := compound_child_constraint_edges htop hgroup hfind
            hchildZip hchildBorder hchildPath hcbfind
          have hchildIn : child.2 ∈ c :=
            X_pushIntoComp hbd hcMem (List.mem_append_right _ he₁) htinc
          have hcbIn : cb.2 ∈ c := hcbprop c hcMem hchildIn
          have h := X_pushIntoComp hbd hcMem (List.mem_append_right _ he₂) hcbIn
          simpa using h
      · have hmemNE : ∃ m : Node × Nat, m ∈ graph.nodes.zipIdx.filter (fun q =>
            q.1.border == 0 && q.1.clusterPath.contains t.1.decl) := by
          cases hl : (graph.nodes.zipIdx.filter (fun q =>
              q.1.border == 0 && q.1.clusterPath.contains t.1.decl)) with
          | nil => rw [hl] at hmemEmpty; exact absurd rfl hmemEmpty
          | cons first rest => exact ⟨first, by simp⟩
        obtain ⟨member, hmember⟩ := hmemNE
        obtain ⟨hmZip, hmPred⟩ := List.mem_filter.mp hmember
        obtain ⟨hbeqBorder, hinside⟩ := Bool.and_eq_true_iff.mp hmPred
        have hmPlain : member.1.border = 0 := by simpa using hbeqBorder
        obtain ⟨he₁, he₂⟩ := compound_member_constraint_edges htop hgroup hfind
          hmZip hmPlain hinside
        have hmemberIn : member.2 ∈ c :=
          X_pushIntoComp hbd hcMem (List.mem_append_right _ he₁) htinc
        have h := X_pushIntoComp hbd hcMem (List.mem_append_right _ he₂) hmemberIn
        simpa using h
  have hlookup : graph.nodes[top.2]? = some top.1 := List.mem_zipIdx_iff_getElem?.mp hmem
  obtain ⟨t0, ht0look, htbord, htpath, htdecl⟩ := X_exactGraph_node_key_rev h hlookup
  have hgroup0 : t0.border = -2 := by rw [← htbord]; exact hgroup
  obtain ⟨hdecl0, box, hbox, _, hpath0⟩ := measuredGraph_group_origin h0 ht0look hgroup0
  have hpath : top.1.clusterPath = Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box ++ [top.1.decl] := by
    rw [htpath, htdecl]; exact hpath0
  have hplen : (Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box).length ≤
      inp.boxes.length := by
    unfold Compound.path
    refine Nat.le_trans (ancestors_length_le _ _ _) ?_
    rw [List.length_map]
    exact Nat.le_refl _
  have hlen : top.1.clusterPath.length ≤ inp.boxes.length + 1 := by
    rw [hpath]
    simp only [List.length_append, List.length_singleton]
    omega
  have htopPos : 0 < top.1.clusterPath.length :=
    Nat.pos_of_ne_zero fun hnil =>
      (X_graph_marker_nonempty h0 h (List.mem_of_getElem?
        (List.mem_zipIdx_iff_getElem?.mp hmem)) hgroup) (List.length_eq_zero_iff.mp hnil)
  obtain ⟨gb, hfind, hprop⟩ := key (inp.boxes.length + 2) top hmem hgroup hlen (by omega)
  have hgbFacts : gb.1.border = 2 ∧ gb.1.decl = top.1.decl := by
    have hp : ((fun e : Node × Nat => e.1.border == 2 && e.1.decl == top.1.decl) gb) = true :=
      List.find?_some (p := fun e : Node × Nat =>
        e.1.border == 2 && e.1.decl == top.1.decl) hfind
    simpa using hp
  have hgbIn : gb.2 ∈ comp := hprop comp hcomp htopinc
  have hlookupGb : graph.nodes[gb.2]? = some gb.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
  have hgb1in : gb.1 ∈ (componentCandidate graph comp candidate).nodes := by
    rw [componentCandidate_nodes]
    exact List.mem_map.mpr ⟨gb.2, hgbIn, by
      rw [List.getD_eq_getElem?_getD, hlookupGb]
      rfl⟩
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp hgb1in
  have hp : ((fun entry : Node × Nat =>
      entry.1.border == 2 && entry.1.decl == top.1.decl) (gb.1, i₀)) = true := by
    simp [hgbFacts.1, hgbFacts.2]
  exact X_findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hi₀) hp

/-- Exact candidate bottom find: replay of `componentRun_cg_bottom_find`. -/
theorem X_componentRun_cg_bottom_find {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {j : Nat} {top : Node}
    (htop : (componentCandidate graph comp candidate).nodes[j]? = some top)
    (hgroup : top.border = -2) :
    ∃ bottom : Node × Nat,
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == top.decl) = some bottom := by
  obtain ⟨oIdx, hoIdx, hsource⟩ := componentCandidate_nonplain_source htop (by omega)
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? hoIdx
  exact X_candidate_group_bottom_find h0 h hlines hcomp candidate (top := (top, oIdx))
    (List.mem_zipIdx_iff_getElem?.mpr hsource) hoIn hgroup

/-- Exact title marker record. Replay of `titled_marker_record`. -/
theorem X_titled_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some (titleF node) := by
  have hnonplain : node.node.border ≠ 0 := by
    rcases hborder with hborder | hborder <;> omega
  have hsized : (sizeProperPortsX P exact source).nodes[index]? = some node := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some,
      Nat.zero_add]
    simp [hnonplain]
  rw [titleReservations_nodes, List.getElem?_append_left (by
    simp only [List.length_map, sizeProperPortsX_length]
    exact (List.getElem?_eq_some_iff.mp hnode).1)]
  simp only [List.getElem?_map, hsized, Option.map_some]

/-- Exact coordinate marker record. Replay of `coordinateGraph_marker_record`. -/
theorem X_coordinateGraph_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2)
    (hdummy : node.dummy = false) :
    (coordinateGraphX P exact source).nodes[index]? = some (clearF (titleF node)) := by
  have htitled := X_titled_marker_record (P := P) (exact := exact) hnode hborder
  obtain ⟨extra, hextension, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  have hbordered : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some (titleF node) := by
    rw [hextension, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitled).1]
    exact htitled
  have hcleared : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
      some (clearF (titleF node)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hbordered]
    rfl
  have hreal : (clearF (titleF node)).dummy = false :=
    (clearF_keys _).1.trans ((titleF_keys node).1.trans hdummy)
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hcleared, Option.map_some,
    Nat.zero_add, hreal, Bool.false_eq_true, ↓reduceIte]

/-- Exact proxy side source. Replay of `componentRun_proxy_side_source`. -/
theorem X_proxy_side_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner sideIndex : Nat) (side : ProperNode),
      node.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, _, _, _⟩ := componentRunX_spec h
  obtain ⟨owner, span, howner, hspan⟩ :=
    proxyWidths_proxy_span_source hproxy hnode hborder
  obtain ⟨sideIndex, side, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    proxySpan_side_source hspan
  exact ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩

/-- Exact coordinate side original. Replay of `coordinateGraph_side_original`. -/
theorem X_side_original {P : Params} {exact : List Nat} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {side : ProperNode}
    (hside : (coordinateGraphX P exact source).nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW).nodes[index]? = some side := by
  have hwf : OrderImpl.BordersWellFormed (coordinateGraphX P exact source) := by
    unfold coordinateGraphX
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed
        (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
        have hz := hwf.2.2 index side hside hd
        rcases hborder with hborder | hborder <;> omega
  obtain ⟨cleared, hcleared, hd, _, _, heq⟩ :=
    materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)) hside
  have hclearedReal : cleared.dummy = false := hd.symm.trans hreal
  have hsame : side = cleared := heq hclearedReal
  have hclearLookup : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some side := by
    rw [hsame]
    exact hcleared
  rw [clearProxyExtents_nodes, List.getElem?_map] at hclearLookup
  obtain ⟨original, horiginal, hclearEq⟩ := Option.map_eq_some_iff.mp hclearLookup
  have hb : side.node.border = original.node.border := by
    rw [← hclearEq]
    exact (clearF_keys original).2.1
  have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
    rwa [hb] at hborder
  have hclearId : clearF original = original := by
    unfold clearF
    rcases hoside with hoside | hoside <;> simp [hoside]
  exact horiginal.trans (congrArg some (hclearId.symm.trans hclearEq))

/-- Exact titled marker source record. Replay of `titled_marker_source_record`. -/
theorem X_titled_marker_source_record {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source)
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {index : Nat} {marker : ProperNode}
    (hmarker : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some marker)
    (hborder : marker.node.border = -2 ∨ marker.node.border = 2) :
    ∃ original : Node, cg.nodes[index]? = some original ∧
      marker.node.border = original.border ∧
      marker = titleF ⟨original, false, none, false⟩ := by
  rcases X_titled_node_origin hkeys hmarker with
    ⟨before, hbefore, _, hb, _⟩ | ⟨_, hb⟩
  · rcases hkeys index before hbefore with
      ⟨original, horiginal, _, hsourceBorder, _⟩ | ⟨_, hplain, _⟩
    · have hborderOriginal : original.border = -2 ∨ original.border = 2 := by
        rcases hborder with hborder | hborder <;> omega
      have hforward := X_titled_marker_record (P := P) (exact := exact)
        (hrecords index original horiginal) hborderOriginal
      exact ⟨original, horiginal, hb.trans hsourceBorder,
        Option.some.inj (hmarker.symm.trans hforward)⟩
    · rcases hborder with hborder | hborder <;> omega
  · rcases hborder with hborder | hborder <;> omega

/-- Exact coordinate side source bundle. Replay of `componentRun_coordinate_side_source`. -/
theorem X_coordinate_side_source {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) {index : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    ∃ (labeled : Proper) (top bottom : ProperNode × Nat),
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      top ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2) ∧
      ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      side.node.clusterPath = top.1.node.clusterPath := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hcoordinate : (coordinateGraphX P exact labeled).nodes[index]? = some side := by
    rw [hc]
    exact hside
  have horiginal := X_side_original hready hcoordinate hborder
  obtain ⟨top, htop, bottom, hbottom, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal) hborder
  exact ⟨labeled, top, bottom, hc, htop, hbottom, hpath⟩

/-- Exact proxy bottom source bundle. Replay of `componentRun_proxy_bottom_source`. -/
theorem X_proxy_bottom_source {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) {index : Nat} {proxy : ProperNode}
    (hproxy : run.coordinateProper.nodes[index]? = some proxy)
    (hborder : proxy.node.border = -2 ∨ proxy.node.border = 2) :
    ∃ (labeled : Proper) (owner sideIndex : Nat) (side : ProperNode)
      (top bottom : ProperNode × Nat),
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      proxy.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index ∧
      top ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2) ∧
      ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      side.node.clusterPath = top.1.node.clusterPath ∧
      top.1.node.clusterPath.getLast? = some owner := by
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    X_proxy_side_source hrun hproxy hborder
  obtain ⟨labeled, top, bottom, hc, htop, hbottom, hpath⟩ :=
    X_coordinate_side_source h0 h hcomp hrun hside hsideBorder
  refine ⟨labeled, owner, sideIndex, side, top, bottom, hc, howner, hside,
    hsideBorder, hsideRank, htop, hbottom, hpath, ?_⟩
  rw [← hpath]
  exact hsideOwner

/-- Exact candidate group path iff decl. Replay of
`componentCandidate_group_path_iff_decl`. -/
theorem X_group_path_iff_decl {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate firstIndex secondIndex : Nat} {first second : Node}
    (hfirst : (componentCandidate graph comp candidate).nodes[firstIndex]? = some first)
    (hsecond : (componentCandidate graph comp candidate).nodes[secondIndex]? = some second)
    (hfirstBorder : first.border = -2) (hsecondBorder : second.border = -2) :
    first.clusterPath = second.clusterPath ↔ first.decl = second.decl := by
  obtain ⟨firstSrc, hfirstSrc, hfirstSource⟩ :=
    componentCandidate_nonplain_source hfirst (by omega)
  obtain ⟨secondSrc, hsecondSrc, hsecondSource⟩ :=
    componentCandidate_nonplain_source hsecond (by omega)
  obtain ⟨f0, hf0look, hfbord, hfpath, hfdecl⟩ := X_exactGraph_node_key_rev h hfirstSource
  obtain ⟨s0, hs0look, hsbord, hspath, hsdecl⟩ := X_exactGraph_node_key_rev h hsecondSource
  have hfirstBorder0 : f0.border = -2 := by rw [← hfbord]; exact hfirstBorder
  have hsecondBorder0 : s0.border = -2 := by rw [← hsbord]; exact hsecondBorder
  obtain ⟨_, firstBox, hfirstBox, _, hfirstPath⟩ :=
    measuredGraph_group_origin h0 hf0look hfirstBorder0
  obtain ⟨_, secondBox, hsecondBox, _, hsecondPath⟩ :=
    measuredGraph_group_origin h0 hs0look hsecondBorder0
  have epath : first.clusterPath = f0.clusterPath := hfpath
  have edecl : first.decl = f0.decl := hfdecl
  have epath2 : second.clusterPath = s0.clusterPath := hspath
  have edecl2 : second.decl = s0.decl := hsdecl
  constructor
  · intro hp
    have hp0 : f0.clusterPath = s0.clusterPath := by
      rw [← epath, ← epath2]; exact hp
    have hlast := congrArg List.getLast? hp0
    have hlastF : f0.clusterPath.getLast? = some f0.decl :=
      X_cg_path_last hfirstPath
    have hlastS : s0.clusterPath.getLast? = some s0.decl :=
      X_cg_path_last hsecondPath
    rw [hlastF, hlastS] at hlast
    have hdeq : f0.decl = s0.decl := Option.some.inj hlast
    rw [edecl, edecl2]; exact hdeq
  · intro hd
    have hd0 : f0.decl = s0.decl := by
      rw [← edecl, ← edecl2]; exact hd
    have hbox : firstBox = secondBox := by
      rw [hd0] at hfirstBox
      exact Option.some.inj (hfirstBox.symm.trans hsecondBox)
    have hp0 : f0.clusterPath = s0.clusterPath := by
      rw [hfirstPath, hsecondPath, hbox, ← hfdecl, ← hsdecl, hd]
    rw [epath, epath2]; exact hp0

/-- Exact titled group owner uniqueness. Replay of `titled_group_owner_unique`. -/
theorem X_titled_group_owner_unique {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {exact : List Nat}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {source : Proper}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) source)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        source.nodes[index]? = some ⟨node, false, none, false⟩)
    {a b : Nat} {first second : ProperNode}
    (hfirst : (titleReservations (sizeProperPortsX P exact source)).nodes[a]? = some first)
    (hsecond : (titleReservations (sizeProperPortsX P exact source)).nodes[b]? = some second)
    (hfirstBorder : first.node.border = -2) (hsecondBorder : second.node.border = -2)
    (howner : first.node.clusterPath.getLast? = second.node.clusterPath.getLast?) : a = b := by
  obtain ⟨oa, hoa, hba, hea⟩ :=
    X_titled_marker_source_record hkeys hrecords hfirst (Or.inl hfirstBorder)
  obtain ⟨ob, hob, hbb, heb⟩ :=
    X_titled_marker_source_record hkeys hrecords hsecond (Or.inl hsecondBorder)
  have hgroupA : oa.border = -2 := hba.symm.trans hfirstBorder
  have hgroupB : ob.border = -2 := hbb.symm.trans hsecondBorder
  have hlastA : first.node.clusterPath.getLast? = some oa.decl := by
    obtain ⟨box, hbox, hpathF⟩ := X_cg_group_box h0 h hoa hgroupA
    have e1 : first.node.clusterPath = oa.clusterPath := by
      rw [hea]; exact (titleF_keys _).2.2.1
    rw [e1]; exact X_cg_path_last hpathF
  have hlastB : second.node.clusterPath.getLast? = some ob.decl := by
    obtain ⟨box, hbox, hpathS⟩ := X_cg_group_box h0 h hob hgroupB
    have e1 : second.node.clusterPath = ob.clusterPath := by
      rw [heb]; exact (titleF_keys _).2.2.1
    rw [e1]; exact X_cg_path_last hpathS
  have hdecl : oa.decl = ob.decl := by
    rw [hlastA, hlastB] at howner
    exact Option.some.inj howner
  have hpath := (X_group_path_iff_decl h0 h hoa hob hgroupA hgroupB).mpr hdecl
  exact (componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate).1 a b oa ob hoa hob hgroupA
    hgroupB hpath

/-- Exact prepared group bottom. Replay of `componentRun_prepared_group_bottom`. -/
theorem X_prepared_group_bottom {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) {labeled : Proper}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hk : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ bottom : ProperNode × Nat,
      (titleReservations (sizeProperPortsX P exact labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have hrequested : (titleReservations (sizeProperPortsX P exact labeled)).nodes[index]? =
      some requested := X_titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have hrequestedBorder : requested.node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans hrequestedBorder
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hsideCoordinate : (coordinateGraphX P exact labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsideOriginal := X_side_original hready hsideCoordinate hsideBorder
  obtain ⟨anchor, hanchor, bottom, hbottom, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsideOriginal) hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? = requested.node.clusterPath.getLast? := by
    rw [← hpath, ← (clearF_keys requested).2.2.1]
    exact hsideOwner.trans howner.symm
  have hindex := X_titled_group_owner_unique h0 h hcomp hk hrecords
    hanchorLookup hrequested hanchorBorder hrequestedBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX P exact labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact hrequested
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  refine ⟨bottom, hrequested, ?_⟩
  have hreqpath : requested.node.clusterPath = node.clusterPath :=
    (titleF_keys _).2.2.1
  rw [hanchorEq] at hbottom
  rw [← hreqpath]
  exact hbottom

/-- Exact titled bottom find source. Replay of `titled_bottom_find_source`. -/
theorem X_titled_bottom_find_source {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source)
    (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      source.nodes[index]? = some ⟨node, false, none, false⟩)
    {path : List Nat} {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 && entry.1.node.clusterPath == path) =
        some bottom) :
    ∃ original : Node, cg.nodes[bottom.2]? = some original ∧
      original.border = 2 ∧ original.clusterPath = path ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      (cg.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.clusterPath == path) = some (original, bottom.2) := by
  have hbottomLookup := List.mem_zipIdx_iff_getElem?.mp
    (List.mem_of_find?_eq_some hfind)
  have hpredicate := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpredicate
  obtain ⟨original, horiginal, hborder, hrecord⟩ :=
    X_titled_marker_source_record hkeys hrecords hbottomLookup (Or.inr hpredicate.1)
  have horiginalBorder : original.border = 2 := hborder.symm.trans hpredicate.1
  have horiginalPath : original.clusterPath = path := by
    simpa [hrecord, titleF, horiginalBorder] using hpredicate.2
  refine ⟨original, horiginal, horiginalBorder, horiginalPath, hrecord, ?_⟩
  obtain ⟨_, position, hposition, hpositionRecord, hbefore⟩ :=
    List.find?_eq_some_iff_getElem.mp hfind
  have hpositionIndex : position = bottom.2 := by
    simpa only [List.getElem_zipIdx, Nat.zero_add] using
      congrArg Prod.snd hpositionRecord
  have hsourceZip : cg.nodes.zipIdx[bottom.2]? = some (original, bottom.2) := by
    simp only [List.getElem?_zipIdx, horiginal, Option.map_some, Nat.zero_add]
  obtain ⟨hsourceBound, hsourceRecord⟩ := List.getElem?_eq_some_iff.mp hsourceZip
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp [horiginalBorder, horiginalPath], bottom.2, hsourceBound,
    hsourceRecord, ?_⟩
  intro earlier hearlier
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  apply Bool.eq_false_iff.mpr
  intro hmatch
  have hearlierSource : earlier < cg.nodes.length := by
    simp only [List.length_zipIdx] at hsourceBound
    omega
  let previous := cg.nodes[earlier]'hearlierSource
  have hprevious : cg.nodes[earlier]? = some previous :=
    List.getElem?_eq_getElem hearlierSource
  have hpreviousMatch : previous.border = 2 ∧ previous.clusterPath = path := by
    simpa only [List.getElem_zipIdx, Nat.zero_add, Bool.and_eq_true, beq_iff_eq] using hmatch
  have hforward := X_titled_marker_record (P := P) (exact := exact)
    (hrecords earlier previous hprevious) (Or.inr hpreviousMatch.1)
  have hprior := hbefore earlier (by omega)
  have htargetZip :
      (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx[earlier]? =
        some (titleF ⟨previous, false, none, false⟩, earlier) := by
    simp only [List.getElem?_zipIdx, hforward, Option.map_some, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.mp htargetZip).2] at hprior
  simp [titleF, hpreviousMatch.1, hpreviousMatch.2] at hprior

/-- Exact candidate bottom lookup keys. Replay of
`componentCandidate_bottom_lookup_keys`. -/
theorem X_bottom_lookup_keys {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate index : Nat} {top : Node}
    (htop : (componentCandidate graph comp candidate).nodes[index]? = some top)
    (hgroup : top.border = -2) :
    ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.clusterPath == top.clusterPath) =
    ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) := by
  obtain ⟨orig, ho, htopSource⟩ := componentCandidate_nonplain_source htop (by omega)
  obtain ⟨t0, ht0look, htbord, htpath, htdecl⟩ := X_exactGraph_node_key_rev h htopSource
  have hgroup0 : t0.border = -2 := by rw [← htbord]; exact hgroup
  apply RankImpl.find?_congr'
  intro entry hentry
  by_cases hb : entry.1.border = 2
  · have hentryLookup := List.mem_zipIdx_iff_getElem?.mp hentry
    obtain ⟨eorig, eho, hbottomSource⟩ :=
      componentCandidate_nonplain_source hentryLookup (by omega)
    obtain ⟨e0, he0look, hebord, hepath, hedecl⟩ := X_exactGraph_node_key_rev h hbottomSource
    have hb0 : e0.border = 2 := by rw [← hebord]; exact hb
    have hkey := measuredGraph_group_bottom_path_iff_decl h0 ht0look hgroup0
      (List.mem_of_getElem? he0look) hb0
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    have epath : entry.1.clusterPath = e0.clusterPath := hepath
    have edecl : entry.1.decl = e0.decl := hedecl
    have tpath : top.clusterPath = t0.clusterPath := htpath
    have tdecl : top.decl = t0.decl := htdecl
    constructor
    · intro h
      obtain ⟨hb1, hpc⟩ := h
      have hcc : e0.clusterPath = t0.clusterPath := by
        rw [← epath, ← tpath]; exact hpc
      have hdd : e0.decl = t0.decl := hkey.mp hcc
      exact ⟨hb1, by rw [edecl, tdecl]; exact hdd⟩
    · intro h
      obtain ⟨hb1, hdd⟩ := h
      have hcc : e0.decl = t0.decl := by
        rw [← edecl, ← tdecl]; exact hdd
      have hpp : e0.clusterPath = t0.clusterPath := hkey.mpr hcc
      exact ⟨hb1, by rw [epath, tpath]; exact hpp⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => (hb h.1).elim, fun h => (hb h.1).elim⟩

/-- Exact candidate titled bottom constraint source. Replay of
`candidate_titled_bottom_constraint_source`. -/
theorem X_bottom_constraint_source {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate index : Nat} {exact : List Nat} {source : Proper} {node : Node}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) source)
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate graph comp candidate).nodes[key]? = some original →
        source.nodes[key]? = some ⟨original, false, none, false⟩)
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
        some bottom) :
    ∃ original : Node,
      (componentCandidate graph comp candidate).nodes[bottom.2]? = some original ∧
      original.border = 2 ∧ original.clusterPath = node.clusterPath ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == node.decl) = some (original, bottom.2) := by
  obtain ⟨original, horiginal, hborder, hpath, hrecord, hsourceFind⟩ :=
    X_titled_bottom_find_source hkeys hrecords hfind
  refine ⟨original, horiginal, hborder, hpath, hrecord, ?_⟩
  rw [← X_bottom_lookup_keys h0 h hnode hgroup]
  exact hsourceFind

/-- Exact group bottom source bundle. Replay of `componentRun_group_bottom_source`. -/
theorem X_group_bottom_source {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady
        (titleReservations (sizeProperPortsX P exact labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPortsX P exact labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) = some bottom := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  obtain ⟨bottom, htitled, hbottom⟩ :=
    X_prepared_group_bottom h0 h hcomp hrun hc hk hready hrecords hnode hgroup
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩

/-- Exact group top ranks strictly below its own bottom marker. Replay of
`componentRun_group_top_lt_bottom`. -/
theorem X_group_top_lt_bottom {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) = .ok rr ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      ∀ (topIndex : Nat) (top : Node) (bottom : Node × Nat),
        (componentCandidate graph comp candidate).nodes[topIndex]? = some top →
        top.border = -2 →
        ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
          entry.1.border == 2 && entry.1.decl == top.decl) = some bottom →
        rk rr.ranks topIndex + 1 ≤ rk rr.ranks bottom.2 := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  refine ⟨rr, labeled, hrr, hc, hk, hrecords, hranks, ?_⟩
  let cg := componentCandidate graph comp candidate
  let maxLen := ((cg.nodes.filter fun n => n.border == -2).map
    (fun n => n.clusterPath.length)).foldr max 0
  have hbound : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath.length ≤ maxLen := by
    intro index node hnode hgroup
    have hmem : node ∈ cg.nodes.filter (fun n => n.border == -2) :=
      List.mem_filter.mpr ⟨List.mem_of_getElem? hnode, by simp [hgroup]⟩
    exact X_le_foldr_max (List.mem_map_of_mem hmem)
  have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath ≠ [] := by
    intro index node hnode hgroup hnil
    exact (X_componentCandidate_marker_shape h0 h hnode).2 hgroup hnil
  have main : ∀ fuel : Nat, ∀ (topIndex : Nat) (top : Node) (bottom : Node × Nat),
      cg.nodes[topIndex]? = some top →
      top.border = -2 →
      (cg.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == top.decl) = some bottom →
      maxLen - top.clusterPath.length = fuel →
      rk rr.ranks topIndex + 1 ≤ rk rr.ranks bottom.2 := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro topIndex top bottom htop hgroup hbottom hfuel
      cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
          entry.1.border == 0 && entry.1.clusterPath.contains top.decl).isEmpty with
      | false =>
        have hmemNe : (cg.nodes.zipIdx.filter fun entry =>
            entry.1.border == 0 && entry.1.clusterPath.contains top.decl) ≠ [] :=
          X_isEmpty_false_ne_nil hmemCase
        obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _ hmemNe
        obtain ⟨hmemberZip, hmemberCond⟩ := List.mem_filter.mp hmember
        obtain ⟨hmemberPlain, hmemberInside⟩ := Bool.and_eq_true_iff.mp hmemberCond
        have hmemberPlain' : member.1.border = 0 := by simpa using hmemberPlain
        have hmemberInside' : member.1.clusterPath.contains top.decl = true := by
          simpa using hmemberInside
        obtain ⟨hleft, hright⟩ := ranked_compound_member_interval hrr
          (top := (top, topIndex)) (bottom := bottom) (member := member)
          (List.mem_zipIdx_iff_getElem?.mpr htop) hgroup hbottom
          hmemberZip hmemberPlain' hmemberInside'
        have hleft' : rk rr.ranks topIndex + 1 ≤ rk rr.ranks member.2 := hleft
        have hright' : rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottom.2 := hright
        omega
      | true =>
        cases hchildCase : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
            fun entry => entry.1.clusterPath.dropLast == top.clusterPath).isEmpty with
        | false =>
          have hchildNe : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
              fun entry => entry.1.clusterPath.dropLast == top.clusterPath) ≠ [] :=
            X_isEmpty_false_ne_nil hchildCase
          obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _ hchildNe
          obtain ⟨hchildTop, hchildPath⟩ := List.mem_filter.mp hchildMem
          obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
          have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
          have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
          obtain ⟨childBottomTitle, _, hchildFind0⟩ :=
            X_prepared_group_bottom h0 h hcomp hrun hc hk hready hrecords
              hchildIndex hchildGroup'
          obtain ⟨childOriginal, _, _, _, _, hchildFind'⟩ :=
            X_bottom_constraint_source h0 h hk hrecords hchildIndex
              hchildGroup' hchildFind0
          have hchildPair : cg.nodes.zipIdx.find? (fun entry =>
              entry.1.border == 2 && entry.1.decl == child.1.decl) =
              some (childOriginal, childBottomTitle.2) := hchildFind'
          have hpathEq : child.1.clusterPath.dropLast = top.clusterPath := by
            simpa using hchildPath
          have hdirect := ranked_compound_child_interval hrr
            (parent := (top, topIndex)) (parentBottom := bottom) (child := child)
            (childBottom := (childOriginal, childBottomTitle.2))
            (List.mem_zipIdx_iff_getElem?.mpr htop) hgroup hbottom
            hchildZip hchildGroup' hpathEq hchildPair
          obtain ⟨hleftDirect, hrightDirect⟩ := hdirect
          have hleftDirect' : rk rr.ranks topIndex + 1 ≤ rk rr.ranks child.2 := hleftDirect
          have hlength : child.1.clusterPath.length =
              top.clusterPath.length + 1 := by
            have hne : top.clusterPath ≠ [] := hnonempty topIndex top htop hgroup
            have hchildNonEmpty : child.1.clusterPath ≠ [] := by
              intro hempty
              rw [hempty, List.dropLast_nil] at hpathEq
              exact hne hpathEq.symm
            rw [← hpathEq, List.length_dropLast]
            have hchildLen := List.length_pos_iff.mpr hchildNonEmpty
            omega
          have hboundChild := hbound child.2 child.1 hchildIndex hchildGroup'
          have hpos : 0 < fuel := by omega
          have hfuelChild : maxLen - child.1.clusterPath.length = fuel - 1 := by omega
          have hih := ih (fuel - 1) (by omega) child.2 child.1
            (childOriginal, childBottomTitle.2) hchildIndex hchildGroup' hchildPair hfuelChild
          have hih' : rk rr.ranks child.2 + 1 ≤ rk rr.ranks (childOriginal, childBottomTitle.2).2 :=
            hih
          omega
        | true =>
          exact ranked_empty_group_interval hrr (top := (top, topIndex)) (bottom := bottom)
            (List.mem_zipIdx_iff_getElem?.mpr htop) hgroup hbottom hmemCase hchildCase
  intro topIndex top bottom htop hgroup hbottom
  exact main (maxLen - top.clusterPath.length) topIndex top bottom htop hgroup hbottom rfl

/-- Exact candidate bottom find returns the candidate's own bottom marker pair. Replay
of `componentCandidate_bottom_find_eq`. -/
theorem X_bottom_find_eq {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
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
  obtain ⟨eJ0, heJ0look, heJbord, _, heJdecl⟩ := X_exactGraph_node_key_rev h hgraphJ
  obtain ⟨eI0, heI0look, heIbord, _, heIdecl⟩ := X_exactGraph_node_key_rev h hgraphI
  have hbJ0 : eJ0.border = 2 := by rw [← heJbord]; exact hjB
  have hbI0 : eI0.border = 2 := by rw [← heIbord]; exact hborder
  have hdJI : eJ0.decl = eI0.decl := by
    have e1 : eJ0.decl = (componentCandidate graph comp candidate).nodes[j].decl := heJdecl.symm
    have e2 : eI0.decl = n.decl := heIdecl.symm
    rw [e1, e2]; exact hjD
  have hpairEq : (eJ0, vJ) = (eI0, vI) :=
    measuredGraph_bottom_pair_eq h0
      (List.mem_zipIdx_iff_getElem?.mpr heJ0look)
      (List.mem_zipIdx_iff_getElem?.mpr heI0look) hbJ0 hbI0 hdJI
  have hvJ : vJ = vI := congrArg Prod.snd hpairEq
  have hji : j = i :=
    nodup_map_inj_aux (fun x => x) (by simpa using components_nodup graph comp hcomp)
      (by rw [← hvJ]; exact hcompJ) hcompI rfl
  omega

/-- Exact bottom-marker uniqueness by declaration. Both entries transport to
the measured graph with the same border and declaration, where the public
pair fact applies; zip indices then agree. -/
private theorem X_bottom_pair_unique {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {eA eB : Node × Nat} (hA : eA ∈ graph.nodes.zipIdx) (hB : eB ∈ graph.nodes.zipIdx)
    (hbA : eA.1.border = 2) (hbB : eB.1.border = 2) (hd : eA.1.decl = eB.1.decl) :
    eA = eB := by
  have hlookA : graph.nodes[eA.2]? = some eA.1 := List.mem_zipIdx_iff_getElem?.mp hA
  have hlookB : graph.nodes[eB.2]? = some eB.1 := List.mem_zipIdx_iff_getElem?.mp hB
  obtain ⟨a0, ha0look, ha0bord, _, ha0decl⟩ := X_exactGraph_node_key_rev h hlookA
  obtain ⟨b0, hb0look, hb0bord, _, hb0decl⟩ := X_exactGraph_node_key_rev h hlookB
  have hmA : (a0, eA.2) ∈ graph0.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr ha0look
  have hmB : (b0, eB.2) ∈ graph0.nodes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hb0look
  have hbA0 : (a0, eA.2).1.border = 2 := by
    show a0.border = 2
    rw [← ha0bord]
    exact hbA
  have hbB0 : (b0, eB.2).1.border = 2 := by
    show b0.border = 2
    rw [← hb0bord]
    exact hbB
  have hd0 : (a0, eA.2).1.decl = (b0, eB.2).1.decl := by
    show a0.decl = b0.decl
    rw [← ha0decl, ← hb0decl]
    exact hd
  have heq := measuredGraph_bottom_pair_eq h0 hmA hmB hbA0 hbB0 hd0
  have heq2 : (a0, eA.2).2 = (b0, eB.2).2 := congrArg Prod.snd heq
  have hidx : eA.2 = eB.2 := heq2
  rw [hidx] at hlookA
  have hfst : eA.1 = eB.1 := Option.some.inj (hlookA.symm.trans hlookB)
  exact Prod.ext hfst hidx

/-- Exact bottom path-decl iff. Transport both members to the measured graph
and apply the public path fact. -/
private theorem X_bottom_path_iff {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {nA nB : Node} (hmemA : nA ∈ graph.nodes) (hmemB : nB ∈ graph.nodes)
    (hbA : nA.border = 2) (hbB : nB.border = 2) :
    nA.clusterPath = nB.clusterPath ↔ nA.decl = nB.decl := by
  obtain ⟨iA, hiA⟩ := List.mem_iff_getElem?.mp hmemA
  obtain ⟨iB, hiB⟩ := List.mem_iff_getElem?.mp hmemB
  obtain ⟨a0, ha0look, ha0bord, ha0path, ha0decl⟩ := X_exactGraph_node_key_rev h hiA
  obtain ⟨b0, hb0look, hb0bord, hb0path, hb0decl⟩ := X_exactGraph_node_key_rev h hiB
  have hbA0 : a0.border = 2 := by rw [← ha0bord]; exact hbA
  have hbB0 : b0.border = 2 := by rw [← hb0bord]; exact hbB
  have hiff := measuredGraph_bottom_path_iff_decl h0 (List.mem_of_getElem? ha0look)
    (List.mem_of_getElem? hb0look) hbA0 hbB0
  rw [ha0path, hb0path, ha0decl, hb0decl]
  exact hiff

/-- Exact paired markers. Apply the public paired-markers fact on the measured
graph, then carry both nodes forward across `exactGraph` (same index, same
key fields). Width/height conclusions are dropped: the exact record only
preserves key fields. -/
private theorem X_paired_markers {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {i : Nat} (hi : i < lines.length) {box : ModelBox}
    (hbox : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box)[i]? = some box)
    (hgroup : box.role = .group) :
    ∃ top bottom : Node,
      graph.nodes[i]? = some top ∧ bottom ∈ graph.nodes ∧
      top.border = -2 ∧ bottom.border = 2 ∧
      top.decl = i ∧ bottom.decl = i ∧
      top.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [i] ∧
      bottom.clusterPath = top.clusterPath := by
  obtain ⟨top0, bot0, htop0, hbotmem0, htb0, hbb0, htd0, hbd0, htpath0, hbpath0, _, _⟩ :=
    measuredGraph_paired_markers h0 hi hbox hgroup
  obtain ⟨top, htoplook, htopbord, htoppath, htopdecl⟩ := exactGraph_node_key h htop0
  obtain ⟨ib, hib⟩ := List.mem_iff_getElem?.mp hbotmem0
  obtain ⟨bot, hbotlook, hbotbord, hbotpath, hbotdecl⟩ := exactGraph_node_key h hib
  refine ⟨top, bot, htoplook, List.mem_of_getElem? hbotlook, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htopbord]; exact htb0
  · rw [hbotbord]; exact hbb0
  · rw [htopdecl]; exact htd0
  · rw [hbotdecl]; exact hbd0
  · rw [htoppath]; exact htpath0
  · rw [hbotpath, hbpath0, ← htoppath]

/-- Exact whole-graph marker shape. Transport the lookup to the measured graph
and apply the public marker-shape fact. -/
private theorem X_graph_marker_shape {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {index : Nat} {node : Node}
    (hnode : graph.nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  obtain ⟨n0, hn0look, hn0bord, hn0path, _⟩ := X_exactGraph_node_key_rev h hnode
  obtain ⟨hdisj, hne⟩ := measuredGraph_marker_shape h0 hn0look
  refine ⟨by simpa [hn0bord] using hdisj, fun hg => ?_⟩
  have hg0 : n0.border = -2 := by rw [← hn0bord]; exact hg
  have hne0 := hne hg0
  rwa [← hn0path] at hne0

/-- Bottom-marker find uniqueness over any graph: a qualifying zip entry is
exactly what `find?` returns. Copy of the private `find?_bottom_eq`. -/
private theorem X_find?_bottom_eq {graph : Graph} {d : Nat} {e : Node × Nat}
    (huniquq : ∀ f : Node × Nat, f ∈ graph.nodes.zipIdx → f.1.border = 2 →
      f.1.decl = d → f = e)
    (hd : e.1.decl = d)
    (he : e ∈ graph.nodes.zipIdx) (hb : e.1.border = 2) :
    graph.nodes.zipIdx.find? (fun x => x.1.border == 2 && x.1.decl == d) = some e := by
  obtain ⟨b, hbf⟩ :=
    X_findSomeOfMember (pred := fun x : Node × Nat => x.1.border == 2 && x.1.decl == d) he
      (by simp [hb, hd])
  have hpred := Bool.and_eq_true_iff.mp
    (List.find?_some (p := fun x : Node × Nat => x.1.border == 2 && x.1.decl == d) hbf)
  rw [huniquq b (List.mem_of_find?_eq_some hbf) (by simpa using hpred.1)
    (by simpa using hpred.2)] at hbf
  exact hbf

/-- Fixed-size demotion lookup. Copy of the private `demote_lookup`. -/
private theorem X_demote_lookup {inp : Input} {i : Nat} {b : ModelBox}
    (h : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box)[i]? = some b) :
    ∃ orig : ModelBox, inp.boxes[i]? = some orig ∧ b.id = orig.id ∧ b.parent = orig.parent ∧
      (b.role = .group →
        ¬(inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id) = true)) ∧
      b = (if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id) then
            { orig with role := .node } else orig) := by
  rw [List.getElem?_map] at h
  cases hop : inp.boxes[i]? with
  | none => rw [hop] at h; simp at h
  | some orig =>
    rw [hop, Option.map_some, Option.some.injEq] at h
    by_cases hfixed : inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == orig.id)
    · have hd : b = ({ orig with role := .node } : ModelBox) :=
        h.symm.trans (ite_eq_left hfixed)
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_,
        by rw [hd, ite_eq_left hfixed]⟩
      intro hrole
      rw [hd] at hrole
      simp at hrole
    · have hd : b = orig :=
        h.symm.trans (ite_eq_right (by simp [hfixed]))
      refine ⟨orig, rfl, by rw [hd], by rw [hd], ?_,
        by rw [hd, ite_eq_right hfixed]⟩
      intro _
      exact hfixed

/-- Fixed-size demotion preserves ids. Copy of the private `demote_id`. -/
private theorem X_demote_id {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) b).id = b.id := by
  intro b _
  dsimp only
  split <;> rfl

/-- Fixed-size demotion preserves parents. Copy of the private `demote_parent`. -/
private theorem X_demote_parent {inp : Input} :
    ∀ b ∈ inp.boxes, ((fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) b).parent = b.parent := by
  intro b _
  dsimp only
  split <;> rfl

/-- Exact bordered-graph node classification. Copy of the private
`X_coordinateGraph0_lookup` from `ExactFlatC2` (private there, so kept as a
private copy here). -/
private theorem X_coordinateGraph0_lookupX (P : Params) (exact : List Nat)
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

/-- Exact coordinate-graph node classification. Copy of the private
`X_coordinateGraph_lookup` from `ExactFlatC2`. -/
private theorem X_coordinateGraph_lookupX (P : Params) (exact : List Nat)
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
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup (clearProxyExtents
    (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact p))
      P.clusterBorderW)) h
  rcases X_coordinateGraph0_lookupX P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
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
/-- Exact candidate bottom marker belongs to a candidate group top with the same
cluster path. Replay of `componentRun_cg_top_of_bottom`: the fuel induction is
identical, with every measured-graph origin fact transported across
`exactGraph` (same index, same key fields) and edge boundedness from the exact
constraint bundle. -/
theorem X_componentRun_cg_top_of_bottom {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    {j : Nat} {bottom : Node}
    (hbot : (componentCandidate graph comp candidate).nodes[j]? = some bottom)
    (hborder : bottom.border = 2) :
    ∃ t : Node × Nat,
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == -2 && entry.1.clusterPath == bottom.clusterPath) = some t := by
  have hbd := X_exactConstraintsBounded h0 h hlines
  have hpathLen : ∀ n : Node, n ∈ graph.nodes → n.border = 2 →
      n.clusterPath.length ≤ inp.boxes.length + 1 := by
    intro n hn hb
    obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, hn0look, hn0bord, hn0path, _⟩ := X_exactGraph_node_key_rev h hidx
    have hb0 : n0.border = 2 := by rw [← hn0bord]; exact hb
    obtain ⟨boxD, hboxD, _, hnpathD, _, _⟩ :=
      measuredGraph_bottom_origin h0 (List.mem_of_getElem? hn0look) hb0
    have hplen : (Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box) boxD).length ≤
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
            { box with role := .node } else box).length := by
      unfold Compound.path
      refine Nat.le_trans (ancestors_length_le _ _ _) ?_
      rw [List.length_map]
      exact Nat.le_refl _
    rw [hn0path, hnpathD, List.length_append, List.length_singleton]
    have hmaplen : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box).length = inp.boxes.length := by
      rw [List.length_map]
    omega
  obtain ⟨oIdx, hoIdx, hsource⟩ := componentCandidate_nonplain_source hbot (by omega)
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? hoIdx
  obtain ⟨b0, hb0look, hb0bord, hb0path, hb0decl⟩ := X_exactGraph_node_key_rev h hsource
  have hb0 : b0.border = 2 := by rw [← hb0bord]; exact hborder
  obtain ⟨boxD, hboxD0, hroleD, hbpathD0, _, _⟩ :=
    measuredGraph_bottom_origin h0 (List.mem_of_getElem? hb0look) hb0
  have hboxD : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box)[bottom.decl]? = some boxD := by
    rw [hb0decl]; exact hboxD0
  have hdbound : bottom.decl < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hboxD).1
    rw [List.length_map] at hi
    omega
  obtain ⟨top0, bot0, htop0, hbotmem, htopborder, hbotborder, htopdecl, hbotdecl,
    htoppath, hbotpath, _, _⟩ :=
    measuredGraph_paired_markers h0 hdbound hboxD hroleD
  obtain ⟨top, htoplook, htopbord, htoppathF, htopdeclF⟩ := exactGraph_node_key h htop0
  obtain ⟨ib, hib⟩ := List.mem_iff_getElem?.mp hbotmem
  obtain ⟨bot, hbotlook, hbotbord, hbotpathF, hbotdeclF⟩ := exactGraph_node_key h hib
  have htb : top.border = -2 := by rw [htopbord]; exact htopborder
  have hbb : bot.border = 2 := by rw [hbotbord]; exact hbotborder
  have htd : top.decl = bottom.decl := by rw [htopdeclF, htopdecl]
  have hbotdeclEq : bot.decl = bottom.decl := by rw [hbotdeclF, hbotdecl]
  have htpath : top.clusterPath = Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) boxD ++ [bottom.decl] := by
    rw [htoppathF]; exact htoppath
  have hbpath : bot.clusterPath = top.clusterPath := by
    rw [hbotpathF, hbotpath, ← htoppathF]
  have hzipTop : (top, top.decl) ∈ graph.nodes.zipIdx := by
    rw [htd]; exact List.mem_zipIdx_iff_getElem?.mpr htoplook
  have hbotmemZip : (bottom, oIdx) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsource
  have main : ∀ fuel : Nat, ∀ t e : Node × Nat,
      t ∈ graph.nodes.zipIdx → t.1.border = -2 → t.1.decl = e.1.decl →
      t.1.clusterPath = e.1.clusterPath → e ∈ graph.nodes.zipIdx → e.1.border = 2 →
      e.2 ∈ comp → inp.boxes.length + 2 - e.1.clusterPath.length = fuel →
      t.2 ∈ comp := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro t e htzip hgroup hdecl hpath hezip hbe hecomp hfuel
      have huniquqE : ∀ f : Node × Nat, f ∈ graph.nodes.zipIdx → f.1.border = 2 →
          f.1.decl = e.1.decl → f = e :=
        fun f hf hfb hfd => X_bottom_pair_unique h0 h hf hezip hfb hbe hfd
      have hfindE : graph.nodes.zipIdx.find? (fun x => x.1.border == 2 && x.1.decl == e.1.decl) =
          some e := X_find?_bottom_eq huniquqE rfl hezip hbe
      have hfindT : graph.nodes.zipIdx.find? (fun x => x.1.border == 2 && x.1.decl == t.1.decl) =
          some e := by
        simp only [hdecl]
        exact hfindE
      cases hmemCase : (graph.nodes.zipIdx.filter fun q =>
          q.1.border == 0 && q.1.clusterPath.contains t.1.decl).isEmpty with
      | false =>
        obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _
          (X_isEmpty_false_ne_nil hmemCase)
        obtain ⟨hmZip, hmCond⟩ := List.mem_filter.mp hmember
        obtain ⟨hmPlain, hmInside⟩ := Bool.and_eq_true_iff.mp hmCond
        have hmPlain' : member.1.border = 0 := by simpa using hmPlain
        have hmInside' : member.1.clusterPath.contains t.1.decl = true := by
          simpa using hmInside
        obtain ⟨he₁, he₂⟩ := compound_member_constraint_edges (graph := graph)
          (top := t) (bottom := e) (member := member) htzip hgroup hfindT
          hmZip hmPlain' hmInside'
        obtain ⟨c, hcMem, hcT, hcH⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he₂)
        have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcH hecomp
        rw [hcEq] at hcT
        obtain ⟨c', hcMem', hcT', hcH'⟩ :=
          components_edge_endpoints hbd (List.mem_append_right _ he₁)
        have hcEq' : c' = comp := components_shared_member_eq hcMem' hcomp hcH' hcT
        rw [hcEq'] at hcT'
        exact hcT'
      | true =>
        cases hchildCase : ((graph.nodes.zipIdx.filter fun q => q.1.border == -2).filter
            fun q => q.1.clusterPath.dropLast == t.1.clusterPath).isEmpty with
        | true =>
          have he₁ := compound_empty_group_constraint_edge (graph := graph)
            (top := t) (bottom := e) htzip hgroup hfindT hmemCase hchildCase
          obtain ⟨c, hcMem, hcT, hcH⟩ :=
            components_edge_endpoints hbd (List.mem_append_right _ he₁)
          have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcH hecomp
          rw [hcEq] at hcT
          exact hcT
        | false =>
          obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _
            (X_isEmpty_false_ne_nil hchildCase)
          obtain ⟨hchildTops, hchildPathEq⟩ := List.mem_filter.mp hchildMem
          obtain ⟨hchildZip, hchildGroupB⟩ := List.mem_filter.mp hchildTops
          have hchildGroup : child.1.border = -2 := by simpa using hchildGroupB
          have hchildPath : child.1.clusterPath.dropLast = t.1.clusterPath := by
            simpa using hchildPathEq
          have hchildSource : graph.nodes[child.2]? = some child.1 :=
            List.mem_zipIdx_iff_getElem?.mp hchildZip
          obtain ⟨c0, hc0look, hc0bord, _, hc0decl⟩ :=
            X_exactGraph_node_key_rev h hchildSource
          have hc0bord' : c0.border = -2 := by rw [← hc0bord]; exact hchildGroup
          obtain ⟨hdeclC0, childBox, hchildBoxL0, hchildRole, _⟩ :=
            measuredGraph_group_origin h0 hc0look hc0bord'
          have hchildBoxL : (inp.boxes.map fun box =>
              if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
                { box with role := .node } else box)[child.1.decl]? = some childBox := by
            rw [hc0decl]; exact hchildBoxL0
          have hchildDbound : child.1.decl < lines.length := by
            have hi := (List.getElem?_eq_some_iff.mp hchildBoxL).1
            rw [List.length_map] at hi
            omega
          obtain ⟨childTop, childBot, hchildTopL, hchildBotMem, hchildTopBorder,
            hchildBotBorder, hchildTopDecl, hchildBotDecl, hchildTopPath, hchildBotPath⟩ :=
            X_paired_markers h0 h hchildDbound hchildBoxL hchildRole
          have hs : graph.nodes[child.1.decl]? = some child.1 := by
            have e : child.1.decl = child.2 := hc0decl.trans hdeclC0
            rw [e]; exact hchildSource
          have h1 : graph.nodes[childTop.decl]? = some childTop := by
            rw [hchildTopDecl]; exact hchildTopL
          rw [hchildTopDecl] at h1
          have hchildTopEq : childTop = child.1 :=
            Option.some.inj (h1.symm.trans hs)
          obtain ⟨cbIdx, hcbIdx⟩ := List.mem_iff_getElem?.mp hchildBotMem
          have hcbZip : (childBot, cbIdx) ∈ graph.nodes.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr hcbIdx
          obtain ⟨cb, hcbfind⟩ :=
            X_findSomeOfMember (pred := fun x : Node × Nat =>
                x.1.border == 2 && x.1.decl == child.1.decl) hcbZip
              (by simp [hchildBotBorder, hchildBotDecl])
          have hcbPred : cb.1.border = 2 ∧ cb.1.decl = child.1.decl := by
            have := List.find?_some
              (p := fun x : Node × Nat => x.1.border == 2 && x.1.decl == child.1.decl)
              hcbfind
            simpa using this
          have hcbMemGet : graph.nodes[cb.2]? = some cb.1 :=
            List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hcbfind)
          have hcbMem : cb.1 ∈ graph.nodes := List.mem_of_getElem? hcbMemGet
          have hcbPathEq : cb.1.clusterPath = child.1.clusterPath := by
            have hiff := X_bottom_path_iff h0 h
              (List.mem_of_getElem? hcbMemGet) (List.mem_of_getElem? hcbIdx)
              hcbPred.1 hchildBotBorder
            have hdeq : cb.1.decl = childBot.decl := hcbPred.2.trans hchildBotDecl.symm
            rw [hiff.mpr hdeq, hchildBotPath, hchildTopEq]
          have hcbFuelEq : inp.boxes.length + 2 - cb.1.clusterPath.length = fuel - 1 := by
            have hlenChild : child.1.clusterPath.length =
                t.1.clusterPath.length + 1 := by
              have hd := congrArg List.length hchildPath
              rw [List.length_dropLast] at hd
              have htne := (X_graph_marker_shape h0 h
                (List.mem_zipIdx_iff_getElem?.mp htzip)).2 hgroup
              have htneLen : 0 < t.1.clusterPath.length :=
                List.length_pos_iff.mpr htne
              omega
            have hlenTE : t.1.clusterPath.length = e.1.clusterPath.length := by
              rw [hpath]
            have hlenCB : cb.1.clusterPath.length = child.1.clusterPath.length := by
              rw [hcbPathEq]
            have hboundCB : cb.1.clusterPath.length ≤ inp.boxes.length + 1 :=
              hpathLen cb.1 hcbMem hcbPred.1
            omega
          obtain ⟨he₁, he₂⟩ := compound_child_constraint_edges (graph := graph)
            (parent := t) (parentBottom := e) (child := child)
            (childBottom := cb) htzip hgroup hfindT
            hchildZip hchildGroup hchildPath hcbfind
          obtain ⟨c, hcMem, hcT, hcH⟩ :=
            components_edge_endpoints hbd (List.mem_append_right _ he₂)
          have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcH hecomp
          rw [hcEq] at hcT
          have hchildComp := ih (fuel - 1) (by
              have hbE : e.1.clusterPath.length ≤ inp.boxes.length + 1 :=
                hpathLen e.1 (List.mem_of_getElem?
                  (List.mem_zipIdx_iff_getElem?.mp hezip)) hbe
              omega) child cb
            hchildZip hchildGroup
            hcbPred.2.symm hcbPathEq.symm
            (List.mem_of_find?_eq_some hcbfind) hcbPred.1 hcT hcbFuelEq
          obtain ⟨c', hcMem', hcT', hcH'⟩ :=
            components_edge_endpoints hbd (List.mem_append_right _ he₁)
          have hcEq' : c' = comp :=
            components_shared_member_eq hcMem' hcomp hcH' hchildComp
          rw [hcEq'] at hcT'
          exact hcT'
  have hpeq : top.clusterPath = bottom.clusterPath := by
    rw [htpath, hb0path, hb0decl, hbpathD0]
  have hconnect := main (inp.boxes.length + 2 - bottom.clusterPath.length)
    (top, top.decl) (bottom, oIdx) hzipTop htb htd
    hpeq
    hbotmemZip hborder hoIn rfl
  rw [componentCandidate_nodes]
  have hmem : top ∈ (componentGraph graph comp).nodes := by
    apply List.mem_map.mpr ⟨top.decl, hconnect, ?_⟩
    rw [List.getD_eq_getElem?_getD, htd, htoplook]
    rfl
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp hmem
  exact X_findSomeOfMember
    (pred := fun entry : Node × Nat =>
      entry.1.border == -2 && entry.1.clusterPath == bottom.clusterPath)
    (entry := (top, i₀))
    (List.mem_zipIdx_iff_getElem?.mpr hi₀)
    (by simp [htb, hpeq])
 /-- Exact parent group top marker is in the component. Replay of
 `candidate_parent_top_exists`. -/
theorem X_candidate_parent_top_exists {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {x : Node × Nat} (hxMem : x ∈ (componentCandidate graph comp candidate).nodes.zipIdx)
    (hxGroup : x.1.border = -2) {outerPrefix : List Nat}
    (_hpre : outerPrefix <+: x.1.clusterPath)
    (hlen : outerPrefix.length < x.1.clusterPath.length)
    (hne : outerPrefix ≠ []) :
    ∃ u : Node × Nat,
      ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == -2 && entry.1.clusterPath == x.1.clusterPath.dropLast) = some u := by
  have hbd := X_exactConstraintsBounded h0 h hlines
  have hzipLookup : (componentCandidate graph comp candidate).nodes[x.2]? = some x.1 :=
    List.mem_zipIdx_iff_getElem?.mp hxMem
  obtain ⟨oIdx, ho, hsource⟩ := componentCandidate_nonplain_source hzipLookup (by omega)
  have hoIn : oIdx ∈ comp := List.mem_of_getElem? ho
  obtain ⟨x0, hx0look, hx0bord, hx0path, hx0decl⟩ := X_exactGraph_node_key_rev h hsource
  have hxGroup0 : x0.border = -2 := by rw [← hx0bord]; exact hxGroup
  obtain ⟨hxdecl0, box_x, hboxx, hrolex, hxpath0⟩ :=
    measuredGraph_group_origin h0 hx0look hxGroup0
  have hxdecl : x.1.decl = oIdx := hx0decl.trans hxdecl0
  have hxpath : x.1.clusterPath = Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box_x ++ [x.1.decl] := by
    rw [hx0path, hx0decl]; exact hxpath0
  obtain ⟨orig_x, horigLookup, hidx, hparentOf, hnotfixed, hdemoteX⟩ :=
    X_demote_lookup hboxx
  have hpathXNe : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box_x ≠ [] := by
    intro hnil
    have hclen : x.1.clusterPath.length = 1 := by rw [hxpath, hnil]; simp
    have hoplen : outerPrefix.length = 0 := by omega
    have hopnil : outerPrefix = [] := List.length_eq_zero_iff.mp hoplen
    exact hne hopnil
  have hdrop : x.1.clusterPath.dropLast = Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) box_x := by
    rw [hxpath, List.dropLast_append_of_ne_nil (l := [x.1.decl]) (by simp)]
    simp
  have hnf : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == orig_x.id) = true) := hnotfixed hrolex
  have hbxOrig : box_x = orig_x := by rw [hdemoteX, ite_eq_right hnf]
  rw [hbxOrig] at hdrop hpathXNe
  have hpxne : orig_x.parent ≠ "" := by
    intro hempty
    refine hpathXNe ?_
    unfold Compound.path
    rw [hempty]
    cases hlen : (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
          { box with role := .node } else box).length with
    | zero => simp [Compound.ancestors]
    | succ n => simp [Compound.ancestors]
  have hboxMem : orig_x ∈ inp.boxes := List.mem_of_getElem? horigLookup
  obtain ⟨parentBox, hparentMem, hpid, hpgroup, hpnotfixed⟩ :=
    framedParents_parent hframed hboxMem hpxne
  have hnp : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == parentBox.id) = true) := by
    intro hc
    rw [hc] at hpnotfixed
    simp at hpnotfixed
  obtain ⟨p₀, hp₀⟩ := List.mem_iff_getElem?.mp hparentMem
  have hfbp : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box)[p₀]? = some parentBox := by
    simp only [List.getElem?_map, hp₀, Option.map_some, ite_eq_right hnp]
  have hp₀bound : p₀ < lines.length := by
    have hi := (List.getElem?_eq_some_iff.mp hfbp).1
    rw [List.length_map] at hi
    omega
  obtain ⟨topP, bottomP, htopPlookup, _, htopPborder, _, htopdecl,
    _, htopPpath, _⟩ :=
    X_paired_markers h0 h hp₀bound hfbp hpgroup
  have hpathOrig : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) orig_x =
      Compound.path inp.boxes orig_x := by
    have h := Compound.path_map inp.boxes (fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) X_demote_id X_demote_parent hboxMem
    rw [ite_eq_right hnf] at h
    exact h
  have hpathParent : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) parentBox =
      Compound.path inp.boxes parentBox := by
    have h := Compound.path_map inp.boxes (fun box =>
      if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
        { box with role := .node } else box) X_demote_id X_demote_parent hparentMem
    rw [ite_eq_right hnp] at h
    exact h
  have hpathStep : Compound.path inp.boxes orig_x =
      Compound.path inp.boxes parentBox ++ [p₀] :=
    Compound.path_of_parent (inputModel inp o) hwf hp₀ horigLookup (by rw [hpid]) hpxne
  have hdropFinal : topP.clusterPath = x.1.clusterPath.dropLast := by
    rw [htopPpath, hpathParent, ← hpathStep, ← hpathOrig, ← hdrop]
  have htopPzip : (topP, p₀) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopPlookup
  have htopZip : (x.1, oIdx) ∈ graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hsource
  obtain ⟨xb, hxbfind⟩ := X_groupTopFind?_some h0 h hlines htopZip hxGroup
  obtain ⟨pb, hpbfind⟩ := X_groupTopFind?_some h0 h hlines htopPzip htopPborder
  obtain ⟨heP, _⟩ := compound_child_constraint_edges htopPzip htopPborder hpbfind
    htopZip hxGroup hdropFinal.symm hxbfind
  obtain ⟨c, hcMem, hcP, hcO⟩ :=
    components_edge_endpoints hbd (List.mem_append_right _ heP)
  have hcEq : c = comp := components_shared_member_eq hcMem hcomp hcO hoIn
  rw [hcEq] at hcP
  have htopPin : topP ∈ (componentCandidate graph comp candidate).nodes := by
    rw [componentCandidate_nodes]
    exact List.mem_map.mpr ⟨p₀, hcP, by
      rw [List.getD_eq_getElem?_getD, htopPlookup]
      rfl⟩
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_getElem?.mp htopPin
  have hp : ((fun entry : Node × Nat =>
      entry.1.border == -2 && entry.1.clusterPath == x.1.clusterPath.dropLast)
      (topP, i₀)) = true := by
    simp [htopPborder, hdropFinal]
  exact X_findSomeOfMember (List.mem_zipIdx_iff_getElem?.mpr hi₀) hp
/-- Transitive exact group-top rank bound. Replay of `cg_nested_top_rank`. -/
theorem X_cg_nested_top_rank {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
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
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ha hbA hb hbB hpre hdelta
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := X_cg_top_unique h0 h hcomp ha hb hbA hbB heq
      subst hab
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        X_prefix_length_lt hpre heq
      have hbne : nb.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape h0 h hb).2 hbB
      have hna_ne : na.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape h0 h ha).2 hbA
      obtain ⟨u, hu⟩ := X_candidate_parent_top_exists h0 h hlines hwf hfp hcomp candidate
        (x := (nb, b)) (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpre hlt hna_ne
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
        X_prefix_of_common_prefix hpre (huPath ▸ X_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      have hIH := ih _ hdeltaU a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
      obtain ⟨bbot, hbbot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp hb hbB
      obtain ⟨ubot, hubot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp huLookup huBorder
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

/-- Exact cg-level rank closure for a group top. Exact counterpart of
`GroupTopSubtreeRankCg`: every exact candidate node whose cluster path
contains the top declaration ranks at or below the top, at ranking-graph
level. -/
def X_GroupTopSubtreeRankCg : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions} {exact : List Nat},
    componentRunX P exact
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    ∃ rr : RankImpl.RankResult,
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      ∀ j : Nat, j < (componentCandidate graph comp candidate).nodes.length →
        ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath.contains
          nd.decl = true →
        rk rr.ranks v ≤ rk rr.ranks j

/-- Cg-level exact rank closure. Replay of `groupTopSubtreeRankCg`. -/
theorem X_GroupTopSubtreeRankCg_holds : X_GroupTopSubtreeRankCg := by
  intro P inp o exactIds lines graph0 graph measured h0 h hlines hwf hfp
    comp hcomp candidate run labels orderOptions exact hrun v nd hnode hborder
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  refine ⟨rr, hrr, ?_⟩
  intro j hj hjpath
  have hjnode : (componentCandidate graph comp candidate).nodes[j]? =
      some ((componentCandidate graph comp candidate).nodes.getD j default) := by
    have h1 := List.getElem?_eq_getElem (l := (componentCandidate graph comp candidate).nodes) hj
    have h2 : (componentCandidate graph comp candidate).nodes[j] =
        (componentCandidate graph comp candidate).nodes.getD j default := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [h2] at h1
    exact h1
  have hshape := (X_componentCandidate_marker_shape h0 h hjnode).1
  rcases hshape with hplain0 | hm2 | h2
  · obtain ⟨bot, hbot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp hnode hborder
    have htop : (nd, v) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hnode
    have hmem : (((componentCandidate graph comp candidate).nodes.getD j default), j) ∈
        (componentCandidate graph comp candidate).nodes.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hjnode
    have hinterv := ranked_compound_member_interval hrr htop hborder hbot hmem hplain0 hjpath
    have htop2 : ((nd, v)).2 = v := rfl
    have hmem2 : ((componentCandidate graph comp candidate).nodes.getD j default, j).2 = j := rfl
    rw [htop2, hmem2] at hinterv
    omega
  · obtain ⟨boxT, hboxT, hpathT⟩ := X_cg_group_box h0 h hnode hborder
    obtain ⟨boxJ, hboxJ, hpathJ⟩ := X_cg_group_box h0 h hjnode hm2
    have hpre : nd.clusterPath <+:
        ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath :=
      X_cg_scope_prefix hwf hboxT hpathT hboxJ hpathJ hjpath
    exact X_cg_nested_top_rank h0 h hlines hwf hfp hcomp candidate hrr
      _ v j nd _ hnode hborder hjnode hm2 hpre rfl
  · have hfind := X_bottom_find_eq h0 h hcomp hjnode h2
    by_cases hdecl : ((componentCandidate graph comp candidate).nodes.getD j default).decl =
        nd.decl
    · rw [hdecl] at hfind
      obtain ⟨rr2, labeled2, hrr2, hc2, hk2, hrecords2, hranks2, H⟩ :=
        X_group_top_lt_bottom h0 h hcomp hrun
      have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
      subst hrrEq
      have hle := H v nd _ hnode hborder hfind
      have h2eq : ((((componentCandidate graph comp candidate).nodes.getD j default),
          j)).2 = j := rfl
      rw [h2eq] at hle
      omega
    · obtain ⟨boxT, hboxT, hpathT⟩ := X_cg_group_box h0 h hnode hborder
      obtain ⟨boxM, hboxM, hpathM⟩ := X_cg_bottom_box h0 h hjnode h2
      have hpre : nd.clusterPath <+:
          ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath :=
        X_cg_scope_prefix hwf hboxT hpathT hboxM hpathM hjpath
      obtain ⟨t, ht⟩ := X_componentRun_cg_top_of_bottom h0 h hlines hcomp hjnode h2
      have htPred := List.find?_some ht
      simp only [Bool.and_eq_true, beq_iff_eq] at htPred
      obtain ⟨htBorder, htPath⟩ := htPred
      have htMem : t ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_of_find?_eq_some ht
      have htLookup : (componentCandidate graph comp candidate).nodes[t.2]? = some t.1 :=
        List.mem_zipIdx_iff_getElem?.mp htMem
      have hpreT : nd.clusterPath <+: t.1.clusterPath := by
        rw [htPath]
        exact hpre
      have htrans := X_cg_nested_top_rank h0 h hlines hwf hfp hcomp candidate hrr
        _ v t.2 nd t.1 hnode hborder htLookup htBorder hpreT rfl
      have hdeclT : t.1.decl =
          ((componentCandidate graph comp candidate).nodes.getD j default).decl := by
        have hlastT : t.1.clusterPath.getLast? = some t.1.decl := by
          obtain ⟨box, hbox, hpathT'⟩ := X_cg_group_box h0 h htLookup htBorder
          exact X_cg_path_last hpathT'
        have hlastM : ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath.getLast? =
            some ((componentCandidate graph comp candidate).nodes.getD j default).decl :=
          X_cg_path_last hpathM
        have h := congrArg List.getLast? htPath
        rw [hlastT, hlastM] at h
        exact Option.some.inj h
      obtain ⟨tbot, htbot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp htLookup htBorder
      rw [← hdeclT] at hfind
      have htbotEq : tbot =
          (((componentCandidate graph comp candidate).nodes.getD j default), j) :=
        Option.some.inj (htbot.symm.trans hfind)
      obtain ⟨rr2, labeled2, hrr2, hc2, hk2, hrecords2, hranks2, H⟩ :=
        X_group_top_lt_bottom h0 h hcomp hrun
      have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
      subst hrrEq
      have hle := H t.2 t.1 tbot htLookup htBorder htbot
      rw [htbotEq] at hle
      have h2eq : ((((componentCandidate graph comp candidate).nodes.getD j default),
          j)).2 = j := rfl
      rw [h2eq] at hle
      omega
/-- Proxy widths rewrite only the width: the cluster path survives. Copy of the
private `proxyWidths_path`. -/
private theorem X_proxyWidths_path {p q : Proper} {xs xs' : List Int}
    (h : proxyWidths p xs = .ok (q, xs')) {v : Nat} {nd qn : ProperNode}
    (hv : p.nodes[v]? = some nd) (hq : q.nodes[v]? = some qn) :
    qn.node.clusterPath = nd.node.clusterPath := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, hok⟩ := X_bind_ok h
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hu
  have hok2 : (Except.ok _ : Except LayoutError (Proper × List Int)) =
      Except.ok (q, xs') := hok
  have hqeq : q = { p with nodes := updated.map (·.1) } :=
    (Prod.mk.inj (Except.ok.inj hok2)).1.symm
  have hmem : (p.nodes.zipIdx[v]?) = some (nd, v) := by
    simp [List.getElem?_zipIdx, hv]
  obtain ⟨b, hb1, hb2⟩ := hidx v (nd, v) hmem
  have hqn : q.nodes[v]? = some b.1 := by
    have h0 : (updated.map (·.1))[v]? = some b.1 := by
      simp only [List.getElem?_map, hb2, Option.map_some]
    have h1 : ({ p with nodes := updated.map (·.1) } : Proper).nodes[v]? =
        some b.1 := h0
    rwa [← hqeq] at h1
  have hqnEq : qn = b.1 := Option.some.inj (hq.symm.trans hqn)
  dsimp only at hb1
  by_cases hcond : (nd.node.border == -2 || nd.node.border == 2) = true
  · simp only [hcond, ↓reduceIte] at hb1
    cases hl : nd.node.clusterPath.getLast? with
    | none => simp [hl] at hb1
    | some owner =>
      simp only [hl] at hb1
      obtain ⟨span, hspan, hb1⟩ := X_bind_ok hb1
      obtain ⟨width, hwidth, hb1⟩ := X_bind_ok hb1
      by_cases hw0 : width < 0
      · simp only [hw0, ↓reduceIte] at hb1
        simp [bind, Except.bind] at hb1
      · simp only [hw0, ↓reduceIte] at hb1
        obtain ⟨center, hcenter, hb1⟩ := X_bind_ok hb1
        have hb1' : (Except.ok _ : Except LayoutError (ProperNode × Int)) =
            Except.ok b := hb1
        have hb1'' := Except.ok.inj hb1'
        subst hb1''
        rw [hqnEq]
  · simp only [hcond] at hb1
    have hb1' : (Except.ok (nd, xs.getD v 0) : Except LayoutError (ProperNode × Int)) =
        Except.ok b := hb1
    have hb1'' := Except.ok.inj hb1'
    subst hb1''
    rw [hqnEq]

/-- Executed exact proper nodes share their coordinate records. Copy of the
private `proper_coord_record` through the exact run equations. -/
private theorem X_proper_coord_record {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = pn.dummy ∧
      cn.node.border = pn.node.border ∧
      cn.node.clusterPath = pn.node.clusterPath := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hord, hxs, hproxy, hdrop,
    hr, hrl, hroutes⟩ := componentRunX_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by
    have h := congrArg Proper.nodes hdrop.symm
    simpa [OrderImpl.dropSynthetic] using h
  rw [hnodes] at hp
  have hlen : i < run.coordinateProper.nodes.length := by
    have h1 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hp).1
    have h2 := (proxyWidths_rel hproxy).2.2.1
    omega
  have hcn : run.coordinateProper.nodes[i]? =
      some (run.coordinateProper.nodes[i]'hlen) := List.getElem?_eq_getElem hlen
  obtain ⟨qn, hqn, hqdum, hqbord, _⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 i _ hcn
  have hqnEq : qn = pn := Option.some.inj (hqn.symm.trans hp)
  have hpath := X_proxyWidths_path hproxy hcn hp
  refine ⟨_, hcn, ?_, ?_, ?_⟩
  · rw [← hqnEq]; exact hqdum.symm
  · rw [← hqnEq]; exact hqbord.symm
  · exact hpath.symm

/-- Exact title-reservation rank prefix. -/
private theorem X_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

/-- Exact titled rank record. Copy of `titled_rank_record`. -/
private theorem X_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := X_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Exact coordinate rank anchor prefix. Copy of the rank half of
`coordinateGraph_anchor_prefix`. -/
private theorem X_coordinateGraph_anchor_prefix (P : Params) (exact : List Nat) (p : Proper) :
    ∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra := by
  obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  obtain ⟨tail, htitle⟩ := X_titled_rank_prefix P exact p
  refine ⟨tail ++ extraRanks, ?_⟩
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
  rw [hr, htitle, List.append_assoc]

/-- Exact coordinate rank record. Copy of `coordinateGraph_rank_record`. -/
private theorem X_coordinateGraph_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := X_coordinateGraph_anchor_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Exact coordinate ranks agree with labeled ranks index-wise. Copy of the
private `coord_rank_eq`. -/
private theorem X_coord_rank_eq {P : Params} {exact : List Nat} {labeled : Proper} {run : Run}
    (hcoord : coordinateGraphX P exact labeled = run.coordinateProper)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {x : Nat} (hx : x < labeled.nodes.length) :
    rk run.coordinateProper.rank x = rk labeled.rank x := by
  have hxr : x < labeled.rank.length := by omega
  have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
    List.getElem?_eq_getElem hxr
  have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
    rw [← hcoord]
    exact X_coordinateGraph_rank_record hlab
  simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

/-- Exact prepared titled original rank. Copy of `prepared_titled_original_rk`. -/
private theorem X_prepared_titled_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact source)).rank index = rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := X_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index

/-- Exact prepared coordinate original rank. Copy of
`prepared_coordinate_original_rk`. -/
private theorem X_prepared_coordinate_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
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
  have hcoordinateLookup := X_coordinateGraph_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

/-- Exact coordinate titled rank record. Copy of
`coordinateGraph_titled_rank_record`. -/
private theorem X_coordinateGraph_titled_rank_record {P : Params} {exact : List Nat}
    {source : Proper} {index : Nat} {rank : Int}
    (h : (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).rank[index]? =
      some rank
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Exact titled copy rank record. Copy of `titled_copy_rank_record`. -/
private theorem X_titled_copy_rank_record {P : Params} {exact : List Nat} {source : Proper}
    (haligned : source.nodes.length = source.rank.length)
    {position : Nat} {entry : ProperNode × Nat}
    (hentry : (titleNodes (sizeProperPortsX P exact source))[position]? = some entry) :
    (titleReservations (sizeProperPortsX P exact source)).rank[source.nodes.length + position]? =
      some (rk source.rank entry.2) := by
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun value => rk source.rank value.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank, List.getElem?_append_right (by omega)]
  have hindex : source.nodes.length + position - source.rank.length = position := by omega
  rw [hindex, List.getElem?_map, hentry]
  rfl

/-- Exact rank source bundle. Replay of `rankSource_of_componentRun`. -/
private theorem X_rankSource_of_componentRun {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget
        (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
            (node.border = -2 → node.clusterPath ≠ [])) := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  exact ⟨rr, labeled, hrr, hc, hk, hranks, hrecords,
    fun index node hnode => X_componentCandidate_marker_shape h0 h hnode⟩

/-- From `toNat` order to `Int` order under nonnegativity. Copy of the private
`toNat_le_of_nonneg`. -/
private theorem X_toNat_le_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a.toNat ≤ b.toNat) : a ≤ b := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by exact_mod_cast h
  omega
/-- Exact side rank interval. Copy of `coordinateGraph_side_rank_bounds`
through the exact side-source fact. -/
private theorem X_coordinateGraph_side_rank_bounds {P : Params} {exact : List Nat}
    {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {node : ProperNode}
    (hnode : (coordinateGraphX P exact source).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find? fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath ∧
        0 ≤ rk (coordinateGraphX P exact source).rank index ∧
        (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
          (rk (coordinateGraphX P exact source).rank index).toNat ∧
        (rk (coordinateGraphX P exact source).rank index).toNat ≤
          (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat := by
  have horiginal := X_side_original hready hnode hside
  exact addClusterBorders_side_rank_bounds _ _ hready horiginal hside

/-- Exact side markers sit at or above their group top. Replay of
`side_marker_rank_ge`. -/
theorem X_side_rank_ge (hcg : X_GroupTopSubtreeRankCg)
    {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hbordV : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hcontains : (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true)
    (hside : (run.proper.nodes.getD i default).node.border = -1 ∨
      (run.proper.nodes.getD i default).node.border = 1) :
    rk run.proper.rank v ≤ rk run.proper.rank i := by
  have erv : rk run.proper.rank v = rk run.coordinateProper.rank v :=
    X_proper_rank_eq_local hrun v
  have eri : rk run.proper.rank i = rk run.coordinateProper.rank i :=
    X_proper_rank_eq_local hrun i
  rw [erv, eri]
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hpi : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨cn, hcn, _, hcbord, hcpath⟩ := X_proper_coord_record hrun hpi
  have hsideC : cn.node.border = -1 ∨ cn.node.border = 1 := by
    rw [hcbord]; exact hside
  have hncL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
    rwa [← hc] at hcn
  obtain ⟨top, htopMem, _, hfindB, hpathEq, hnn, hlo, _⟩ :=
    X_coordinateGraph_side_rank_bounds hready hncL hsideC
  have htopGet : (titleReservations (sizeProperPortsX P exact labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
  have htopBorder : top.1.node.border = -2 := by
    simpa using (List.mem_filter.mp htopMem).2
  obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
    X_titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
  have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
    rw [htopRecord]; exact (titleF_keys _).2.2.1
  have hcnContains : cn.node.clusterPath.contains nd.decl = true := by
    rw [hcpath]; exact hcontains
  have htopContains : top.1.node.clusterPath.contains nd.decl = true := by
    rw [← hpathEq]; exact hcnContains
  have htopOrigContains : topOrig.clusterPath.contains nd.decl = true := by
    rw [← htopPath]; exact htopContains
  have hlt : top.2 < (componentCandidate graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp htopCg).1
  have hgetDTop : (componentCandidate graph comp candidate).nodes.getD top.2 default =
      topOrig := by
    rw [List.getD_eq_getElem?_getD, htopCg, Option.getD_some]
  have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD top.2
      default).clusterPath.contains nd.decl = true := by
    rw [hgetDTop]; exact htopOrigContains
  obtain ⟨rr2, hrr2, hclose⟩ := hcg h0 h hlines hwf hfp hcomp hrun hvGet hbordV
  have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
  subst hrrEq
  have hle : rk rr.ranks v ≤ rk rr.ranks top.2 := hclose top.2 hlt hgetDContains
  have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := X_prepared_coordinate_original_rk (P := P) (exact := exact) hrr hranks hvcg
    rw [← hc]; exact h1
  have hTtitle : rk (titleReservations (sizeProperPortsX P exact labeled)).rank top.2 =
      rk rr.ranks top.2 :=
    (X_prepared_titled_original_rk (P := P) (exact := exact) hrr hranks hlt).1
  have hBcoord : rk (coordinateGraphX P exact labeled).rank i = rk run.coordinateProper.rank i := by
    rw [hc]
  have hTnn : 0 ≤ rk (titleReservations (sizeProperPortsX P exact labeled)).rank top.2 := by
    rw [hTtitle]; exact rankWithBudget_rk_nonneg hrr top.2
  have hTopLe : rk (titleReservations (sizeProperPortsX P exact labeled)).rank top.2 ≤
      rk (coordinateGraphX P exact labeled).rank i :=
    X_toNat_le_of_nonneg hTnn hnn hlo
  have hTopCoord : rk rr.ranks top.2 ≤ rk run.coordinateProper.rank i := by
    rw [← hTtitle, ← hBcoord]; exact hTopLe
  rw [hVcoord]
  exact Int.le_trans hle hTopCoord
/-- Exact title rank source. Copy of `coordinateGraph_title_rank_source`
through the exact coordinate classification. -/
private theorem X_coordinateGraph_title_rank_source {cg : Graph} {P : Params}
    {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (haligned : source.nodes.length = source.rank.length)
    {titleIndex : Nat} {title : ProperNode}
    (htitle : (coordinateGraphX P exact source).nodes[titleIndex]? = some title)
    (hborder : title.node.border = 3) :
    ∃ (originalIndex : Nat) (original : ProperNode),
      source.nodes[originalIndex]? = some original ∧
      original.node.border = -2 ∧ original.dummy = false ∧
      title.dummy = false ∧ title.node.clusterPath = original.node.clusterPath ∧
      rk (coordinateGraphX P exact source).rank titleIndex = rk source.rank originalIndex := by
  rcases X_coordinateGraph_lookupX P exact source htitle with
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
      X_sizeProperPorts_node_origin P exact source hsized
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
    have htitledRank := X_titled_copy_rank_record haligned hentry
    have hcoordinateRank := X_coordinateGraph_titled_rank_record htitledRank
    refine ⟨entry.2, original, horiginal, hsourceGroup, horiginalReal,
      htitleReal, htitlePath, ?_⟩
    rw [hindex]
    simp only [rk, List.getD_eq_getElem?_getD, hcoordinateRank, Option.getD_some]

/-- Exact title copies share their anchor top rank. Replay of
`title_copy_rank_ge`. -/
theorem X_title_rank_ge (hcg : X_GroupTopSubtreeRankCg)
    {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hbordV : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hcontains : (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true)
    (hb3 : (run.proper.nodes.getD i default).node.border = 3) :
    rk run.proper.rank v ≤ rk run.proper.rank i := by
  have erv : rk run.proper.rank v = rk run.coordinateProper.rank v :=
    X_proper_rank_eq_local hrun v
  have eri : rk run.proper.rank i = rk run.coordinateProper.rank i :=
    X_proper_rank_eq_local hrun i
  rw [erv, eri]
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate
  have hpi : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨cn, hcn, _, hcbord, hcpath⟩ := X_proper_coord_record hrun hpi
  have hncL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
    rwa [← hc] at hcn
  have hb3C : cn.node.border = 3 := by
    rw [hcbord]; exact hb3
  obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath,
      htitleRank⟩ :=
    X_coordinateGraph_title_rank_source hk hshape haligned hncL hb3C
  have hcnContains : cn.node.clusterPath.contains nd.decl = true := by
    rw [hcpath]; exact hcontains
  have horigContains : original.node.clusterPath.contains nd.decl = true := by
    rw [← htitlePath]; exact hcnContains
  rcases hk originalIndex original horiginal with
    ⟨n, hn, _, hborderN, hpathN⟩ | ⟨hdT, _, _⟩
  · have hnBorder : n.border = -2 := hborderN.symm.trans hOrigBorder
    have hncN : n.clusterPath.contains nd.decl = true := by
      rw [← hpathN]; exact horigContains
    have hlt : originalIndex < (componentCandidate graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp hn).1
    have hgetDOrig : (componentCandidate graph comp candidate).nodes.getD originalIndex
        default = n := by
      rw [List.getD_eq_getElem?_getD, hn, Option.getD_some]
    have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD
        originalIndex default).clusterPath.contains nd.decl = true := by
      rw [hgetDOrig]; exact hncN
    obtain ⟨rr2, hrr2, hclose⟩ := hcg h0 h hlines hwf hfp hcomp hrun hvGet hbordV
    have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
    subst hrrEq
    have hle : rk rr.ranks v ≤ rk rr.ranks originalIndex :=
      hclose originalIndex hlt hgetDContains
    have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
      have h1 := X_prepared_coordinate_original_rk (P := P) (exact := exact) hrr hranks hvcg
      rw [← hc]; exact h1
    have hOcoord : rk run.coordinateProper.rank originalIndex = rk rr.ranks originalIndex := by
      have h1 := X_prepared_coordinate_original_rk (P := P) (exact := exact) hrr hranks hlt
      rw [← hc]; exact h1
    have hrankEq : rk run.coordinateProper.rank i = rk labeled.rank originalIndex := by
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
      have htitLook := X_titled_rank_record (P := P) (exact := exact) hlabLook
      have hcoordLook := X_coordinateGraph_titled_rank_record htitLook
      simp only [rk, List.getD_eq_getElem?_getD, hlabLook, hcoordLook,
        Option.getD_some]
    rw [hVcoord, hrankEq, hlabEq, hOcoord]
    exact hle
  · rw [hdT] at hOrigReal
    simp at hOrigReal
/-- Exact plain dummy border. Copy of `pc_plain` through the exact coordinate
classification. -/
private theorem X_pc_plain {cg : Graph} {P : Params} {exact : List Nat} {labeled : Proper}
    (hK : NodeKeys cg labeled)
    {v : Nat} {nd : ProperNode} (h : (coordinateGraphX P exact labeled).nodes[v]? = some nd)
    (hd : nd.dummy = true) : nd.node.border = 0 := by
  rcases X_coordinateGraph_lookupX P exact labeled h with
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

/-- Exact labeled nodes and ranks stay aligned. Copy of the private
`labeled_rank_aligned`. -/
private theorem X_labeled_rank_aligned {cg : Graph}
    {rr : RankImpl.RankResult} {normalized labeled : Proper}
    {labels : List MeasuredLabel}
    (hnormalize : normalize cg rr.ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
    labeled.nodes.length = labeled.rank.length := by
  have h1 := addLabelNodes_node_length hlabels
  have h2 := congrArg List.length (Labels.addLabelNodes_metadata hlabels).2.1
  have h3 := (normalize_node_rank_alignment hnormalize).1
  omega
/-- An executed exact proper dummy has the same record in the exact coordinate
graph. Copy of the private `proper_to_coordinate_dummy`. -/
private theorem X_proper_to_coordinate_dummy {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
      cn.node.border = pn.node.border ∧ cn.node.clusterPath = pn.node.clusterPath := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
  have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
    (proxyWidths_rel hprox).2.2.1
  have hiC : i < run.coordinateProper.nodes.length := by
    have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
    omega
  obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
    ⟨_, List.getElem?_eq_getElem hiC⟩
  obtain ⟨nd', hnd', hddum, _, _⟩ :=
    (proxyWidths_rel hprox).2.2.2.2.1 i cn hcn
  have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
  have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
  have hK : NodeKeys cg labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hcnL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
    rw [hc]; exact hcn
  have hbord0 : cn.node.border = 0 := X_pc_plain hK hcnL hcnDum
  have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
    rw [hbord0]; decide
  obtain ⟨hsame, _⟩ := (proxyWidths_rel hprox).2.2.2.2.2 i cn hcn hnp
  have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
  exact ⟨cn, hcn, hcnDum, by rw [hcnEq], by rw [hcnEq]⟩

/-- Exact chain rank positions. Copy of the private
`normalize_chain_rank_positions`. -/
private theorem X_normalize_chain_rank_positions {graph : Graph} {ranks : List Int}
    {normalized : Proper} (hnormalize : normalize graph ranks = .ok normalized)
    {index : Nat} {edge : Edge} {chain : List Nat}
    (hedge : graph.edges[index]? = some edge)
    (hchain : normalized.chains[index]? = some chain) :
    ∀ position (hposition : position < chain.length),
      rk normalized.rank (chain[position]'hposition) =
        rk normalized.rank edge.tail + (position : Int) := by
  have hindex := (List.getElem?_eq_some_iff.mp hedge).1
  have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
  by_cases hself : edge.tail = edge.head
  · have hempty : chain = [] := by
      have h := hfact.2
      simp only [hself, ↓reduceIte] at h
      exact Option.some.inj (hchain.symm.trans h)
    intro position hposition
    simp only [hempty, List.length_nil] at hposition
    omega
  · obtain ⟨actual, hactual, _, hhead, _, hadjacent⟩ :
        ∃ actual, normalized.chains[index]? = some actual ∧
          2 ≤ actual.length ∧ actual.head? = some edge.tail ∧
          actual.getLast? = some edge.head ∧
          ∀ (j : Nat) (hj : j < actual.length) (hj1 : j + 1 < actual.length),
            ∃ pe ∈ normalized.edges, pe.original = index ∧ pe.decl = edge.decl ∧
              pe.tail = actual[j] ∧ pe.head = actual[j + 1] := by
      simpa only [hself, ↓reduceIte] using hfact.2
    have hactualEq : chain = actual := Option.some.inj (hchain.symm.trans hactual)
    subst actual
    intro position
    induction position with
    | zero =>
      intro hposition
      have hzero : chain[0]? = some edge.tail := by
        rw [← List.head?_eq_getElem?]
        exact hhead
      have hfirst : chain[0]'hposition = edge.tail :=
        Option.some.inj ((List.getElem?_eq_getElem hposition).symm.trans hzero)
      rw [hfirst]
      change rk normalized.rank edge.tail = rk normalized.rank edge.tail + (0 : Int)
      omega
    | succ position ih =>
      intro hposition
      have hprevious : position < chain.length := by omega
      obtain ⟨pe, hpe, _, _, htail, hnext⟩ := hadjacent position hprevious hposition
      have hstep := normalize_proper graph ranks normalized hnormalize pe hpe
      unfold Proper.span at hstep
      rw [htail, hnext] at hstep
      have hprefix := ih hprevious
      omega

/-- Exact labeled chain rank positions. Copy of
`componentRun_labeled_chain_rank_positions`. -/
private theorem X_labeled_chain_rank_positions
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      ∀ (index : Nat) (edge : Edge) (chain : List Nat),
        cg.edges[index]? = some edge → labeled.chains[index]? = some chain →
        ∀ position (hposition : position < chain.length),
          rk labeled.rank (chain[position]'hposition) =
            rk labeled.rank edge.tail + (position : Int) := by
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, _⟩ :=
    X_componentRun_ranked_source hrun
  refine ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, ?_⟩
  intro index edge chain hedge hchain position hposition
  have metadata := Labels.addLabelNodes_metadata hlabels
  rw [metadata.2.2.1] at hchain
  rw [metadata.2.1]
  exact X_normalize_chain_rank_positions hnormalize hedge hchain position hposition
/-- Exact dummy path chain source. Copy of
`componentRun_dummy_path_chain_source` with exact sizing. -/
private theorem X_dummy_path_chain_source
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v owner : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hdummy : node.dummy = true) (howner : owner ∈ node.node.clusterPath) :
    ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper)
      (index : Nat) (edge : Edge) (chain : List Nat) (position : Nat),
      rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
      normalize cg rr.ranks = .ok normalized ∧
      Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      cg.edges[index]? = some edge ∧ labeled.chains[index]? = some chain ∧
      chain[position]? = some v ∧ chain.head? = some edge.tail ∧
      chain.getLast? = some edge.head ∧
      rk labeled.rank v = rk labeled.rank edge.tail + (position : Int) ∧
      let prepared := clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
      prepared.chains.find? (fun members => members.contains v) = some chain ∧
      owner ∈ (prepared.nodes.getD (chain.headD v) default).node.clusterPath ∧
      owner ∈ (prepared.nodes.getD (chain.getLastD v) default).node.clusterPath := by
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordinate, hpositions⟩ :=
    X_labeled_chain_rank_positions hrun
  let prepared := clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)
  have hmaterialized : (materializeDummyPaths prepared).nodes[v]? = some node := by
    rw [← hcoordinate] at hv
    exact hv
  obtain ⟨before, hbefore, hd, _, _, _⟩ := materialize_lookup prepared hmaterialized
  have hbeforeDummy : before.dummy = true := hd.symm.trans hdummy
  have hpath : node.node.clusterPath = OrderImpl.nodePath prepared v := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
      hbefore, Option.map_some, hbeforeDummy, ↓reduceIte, Option.some.injEq] at hmaterialized
    rw [← hmaterialized]
    simp only [Nat.zero_add]
  have hselected : node.node.clusterPath =
      match prepared.chains.find? (fun members => members.contains v) with
      | none => []
      | some chain => OrderImpl.commonPath
          ((prepared.nodes.getD (chain.headD v) default).node.clusterPath)
          ((prepared.nodes.getD (chain.getLastD v) default).node.clusterPath) := by
    rw [hpath]
    simp [OrderImpl.nodePath, List.getD_eq_getElem?_getD, hbefore, hbeforeDummy]
    rfl
  cases hfind : prepared.chains.find? (fun members => members.contains v) with
  | none =>
    simp only [hfind] at hselected
    rw [hselected] at howner
    exact False.elim (List.not_mem_nil howner)
  | some chain =>
    have hchains : prepared.chains = labeled.chains := by
      exact (OrderImpl.addClusterBorders_metadata
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).2.1
    have hchainMember : chain ∈ prepared.chains := List.mem_of_find?_eq_some hfind
    rw [hchains] at hchainMember
    obtain ⟨index, hchain⟩ := List.mem_iff_getElem?.mp hchainMember
    have hnormalizedChain : normalized.chains[index]? = some chain := by
      rw [← (Labels.addLabelNodes_metadata hlabels).2.2.1]
      exact hchain
    have hindex : index < cg.edges.length := by
      have hbound := (List.getElem?_eq_some_iff.mp hnormalizedChain).1
      rw [normalize_chains_length hnormalize] at hbound
      exact hbound
    have hedge : cg.edges[index]? = some (cg.edges[index]'hindex) :=
      List.getElem?_eq_getElem hindex
    have hmember : v ∈ chain := by
      simpa only [List.contains_iff_mem] using List.find?_some hfind
    obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hmember
    have hpositionBound := (List.getElem?_eq_some_iff.mp hposition).1
    have hpositionValue : chain[position]'hpositionBound = v :=
      Option.some.inj ((List.getElem?_eq_getElem hpositionBound).symm.trans hposition)
    have hfact := (normalize_ok hnormalize).2.2 index hindex _ hedge
    by_cases hself : (cg.edges[index]'hindex).tail = (cg.edges[index]'hindex).head
    · have hempty : chain = [] := by
        have h := hfact.2
        simp only [hself, ↓reduceIte] at h
        exact Option.some.inj (hnormalizedChain.symm.trans h)
      rw [hempty] at hmember
      exact False.elim (List.not_mem_nil hmember)
    · obtain ⟨actual, hactual, _, hhead, hlast, _⟩ := by
        simpa only [hself, ↓reduceIte] using hfact.2
      have hactualEq : chain = actual :=
        Option.some.inj (hnormalizedChain.symm.trans hactual)
      subst actual
      have hrank := hpositions index _ chain hedge hchain position hpositionBound
      rw [hpositionValue] at hrank
      have hownerCommon := howner
      rw [hselected, hfind] at hownerCommon
      obtain ⟨hleftOwner, hrightOwner⟩ := commonPath_member_both _ _ hownerCommon
      exact ⟨rr, normalized, labeled, index, _, chain, position, hrr, hnormalize,
        hlabels, hcoordinate, hedge, hchain, hposition, hhead, hlast, hrank,
        hfind, hleftOwner, hrightOwner⟩

/-- Exact prepared nodes keep their labeled cluster path. Copy of the private
`prepared_path_eq` with exact sizing. -/
private theorem X_prepared_path_eq {P : Params} {exact : List Nat} {labeled : Proper}
    {j : Nat} {pn : ProperNode}
    (hlab : labeled.nodes[j]? = some pn) :
    ∃ qn, (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[j]? =
      some qn ∧ qn.node.clusterPath = pn.node.clusterPath := by
  have hj : j < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hlab).1
  have hlen1 : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
    simp [sizeProperPortsX]
  have hs1 := sizeProperPortsX_key P exact labeled j
  rw [hlab] at hs1
  obtain ⟨m1, hm1, htrip⟩ : ∃ m1, (sizeProperPortsX P exact labeled).nodes[j]? = some m1 ∧
      (m1.dummy, m1.node.border, m1.node.clusterPath) =
        (pn.dummy, pn.node.border, pn.node.clusterPath) := by
    cases hs : (sizeProperPortsX P exact labeled).nodes[j]? with
    | none => simp [hs] at hs1
    | some m1 =>
      simp only [hs, Option.map_some, Option.some.injEq] at hs1
      exact ⟨m1, rfl, hs1⟩
  have hp1 : m1.node.clusterPath = pn.node.clusterPath := by
    have h3 := congrArg (fun t : Bool × Int × List Nat => t.2.2) htrip
    simpa using h3
  have hm2 : (titleReservations (sizeProperPortsX P exact labeled)).nodes[j]? =
      some (titleF m1) := by
    have hJ : j < ((sizeProperPortsX P exact labeled).nodes.map titleF).length := by
      rw [List.length_map, hlen1]; exact hj
    rw [titleReservations_nodes, List.getElem?_append_left hJ, List.getElem?_map, hm1,
      Option.map_some]
  have hp2 : (titleF m1).node.clusterPath = pn.node.clusterPath := by
    rw [(titleF_keys m1).2.2.1]; exact hp1
  have hlen2 : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
      (sizeProperPortsX P exact labeled).nodes.length +
        ((titleNodes (sizeProperPortsX P exact labeled)).map copyF).length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
  have hj2 : j < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    omega
  obtain ⟨extra, hx, _⟩ :=
    addClusterBorders_extra (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hm3 : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[j]? =
      (titleReservations (sizeProperPortsX P exact labeled)).nodes[j]? := by
    rw [hx]; exact List.getElem?_append_left hj2
  have hm4 : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[j]? =
      some (clearF (titleF m1)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hm3, hm2, Option.map_some]
  have hp4 : (clearF (titleF m1)).node.clusterPath = pn.node.clusterPath := by
    rw [(clearF_keys (titleF m1)).2.2.1]; exact hp2
  exact ⟨_, hm4, hp4⟩

/-- Every executed exact proper dummy lies on its original edge chain between
its endpoint ranks. Copy of `dummy_chain_bracket`. -/
private theorem X_dummy_chain_bracket {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hdummy : (run.proper.nodes.getD i default).dummy = true)
    {owner : Nat} (howner : owner ∈ (run.proper.nodes.getD i default).node.clusterPath) :
    ∃ (index : Nat) (edge : Edge),
      cg.edges[index]? = some edge ∧
      edge.tail ≠ edge.head ∧
      edge.tail < cg.nodes.length ∧ edge.head < cg.nodes.length ∧
      rk run.coordinateProper.rank edge.tail ≤ rk run.coordinateProper.rank i ∧
      rk run.coordinateProper.rank i ≤ rk run.coordinateProper.rank edge.head ∧
      ∃ (nA nB : Node),
        cg.nodes[edge.tail]? = some nA ∧ cg.nodes[edge.head]? = some nB ∧
        nA.clusterPath.contains owner = true ∧ nB.clusterPath.contains owner = true := by
  have hp : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨cn, hcn, hcnDum, _, hcnPath⟩ := X_proper_to_coordinate_dummy hrun hp hdummy
  have hownerC : owner ∈ cn.node.clusterPath := by rw [hcnPath]; exact howner
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordRun, hpositions⟩ :=
    X_labeled_chain_rank_positions hrun
  obtain ⟨rrC, normC, labC, index, edge, chain, position,
      hrrC, hnormC, hlabC, hcoordC, hedge, hchainC, hpos, hhead, hlast, hrankC,
      _hfind, hleftC, hrightC⟩ :=
    X_dummy_path_chain_source hrun hcn hcnDum hownerC
  have e1 : rr = rrC := Except.ok.inj (hrr.symm.trans hrrC)
  subst e1
  have e2 : normalized = normC := Except.ok.inj (hnormalize.symm.trans hnormC)
  subst e2
  have e3 : labeled = labC := Except.ok.inj (hlabels.symm.trans hlabC)
  subst e3
  have hindex : index < cg.edges.length := (List.getElem?_eq_some_iff.mp hedge).1
  have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnormalize).2
  have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
  obtain ⟨htailLt, hheadLt, _⟩ := RankImpl.wellformed_spec hwf edge hedgeMem
  have hchainsEq : labeled.chains = normalized.chains :=
    (Labels.addLabelNodes_metadata hlabels).2.2.1
  have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
  have hne : edge.tail ≠ edge.head := by
    intro heq
    have hif := hfact.2
    simp only [heq, ↓reduceIte] at hif
    rw [← hchainsEq] at hif
    have hempty : chain = [] := Option.some.inj (hchainC.symm.trans hif)
    rw [hempty] at hpos
    simp at hpos
  have hlastElem : chain[chain.length - 1]? = some edge.head := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hlastLt : chain.length - 1 < chain.length :=
    (List.getElem?_eq_some_iff.mp hlastElem).1
  have hposLen : position < chain.length := (List.getElem?_eq_some_iff.mp hpos).1
  have hlastEq : chain[chain.length - 1]'hlastLt = edge.head :=
    Option.some.inj ((List.getElem?_eq_getElem hlastLt).symm.trans hlastElem)
  have hlastRank := hpositions index edge chain hedge hchainC (chain.length - 1) hlastLt
  rw [hlastEq] at hlastRank
  have hlabLe1 : rk labeled.rank edge.tail ≤ rk labeled.rank i := by omega
  have hlabLe2 : rk labeled.rank i ≤ rk labeled.rank edge.head := by omega
  have hlenN := normalize_nodes_length_le hnormalize
  have hlenL : normalized.nodes.length = labeled.nodes.length :=
    addLabelNodes_node_length hlabels
  have htailL : edge.tail < labeled.nodes.length := by omega
  have hheadL : edge.head < labeled.nodes.length := by omega
  have haligned := X_labeled_rank_aligned hnormalize hlabels
  have hK : NodeKeys cg labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hnormalize) hlabels
  have hcnL : (coordinateGraphX P exact labeled).nodes[i]? = some cn := by
    rw [hcoordRun]; exact hcn
  have hiL : i < labeled.nodes.length := by
    rcases X_coordinateGraph_lookupX P exact labeled hcnL with
      ⟨m, hm, _, _, _, _⟩ | ⟨hdF, _⟩ | ⟨_, tq, htq, _, hdT, _, _⟩
    · exact (List.getElem?_eq_some_iff.mp hm).1
    · rw [hcnDum] at hdF; exact absurd hdF (by decide)
    · obtain ⟨hs, hbq⟩ := titleNodes_spec htq
      have hk := sizeProperPortsX_key P exact labeled tq.2
      rw [hs] at hk
      cases hp2 : labeled.nodes[tq.2]? with
      | none => simp [hp2] at hk
      | some mp =>
        simp only [hp2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK tq.2 mp hp2 with ⟨_, _, hmd, _, _⟩ | ⟨_, hbB, _⟩
        · rw [hdT, hk1, hmd] at hcnDum; exact absurd hcnDum (by decide)
        · rw [hk2] at hbq; rw [hbB] at hbq; exact absurd hbq (by decide)
  have hcTail : rk run.coordinateProper.rank edge.tail = rk labeled.rank edge.tail :=
    X_coord_rank_eq hcoordRun haligned htailL
  have hcHead : rk run.coordinateProper.rank edge.head = rk labeled.rank edge.head :=
    X_coord_rank_eq hcoordRun haligned hheadL
  have hcI : rk run.coordinateProper.rank i = rk labeled.rank i :=
    X_coord_rank_eq hcoordRun haligned hiL
  have hleC1 : rk run.coordinateProper.rank edge.tail ≤ rk run.coordinateProper.rank i := by
    omega
  have hleC2 : rk run.coordinateProper.rank i ≤ rk run.coordinateProper.rank edge.head := by
    omega
  obtain ⟨nA, hnA⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
    ⟨_, List.getElem?_eq_getElem htailLt⟩
  obtain ⟨nB, hnB⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
    ⟨_, List.getElem?_eq_getElem hheadLt⟩
  have hlabT : labeled.nodes[edge.tail]? = some ⟨nA, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnA
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  have hlabH : labeled.nodes[edge.head]? = some ⟨nB, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnB
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  obtain ⟨qT, hqT, hpT⟩ := X_prepared_path_eq hlabT
  obtain ⟨qH, hqH, hpH⟩ := X_prepared_path_eq hlabH
  have hheadD : chain.headD i = edge.tail := by
    cases hcchain : chain with
    | nil => simp [hcchain] at hhead
    | cons a as =>
      simp only [List.headD]
      simpa [hcchain] using hhead
  have hlastD : chain.getLastD i = edge.head := by
    rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
  have hgetDT : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes.getD
      edge.tail default = qT := by
    rw [List.getD_eq_getElem?_getD, hqT, Option.getD_some]
  have hgetDH : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes.getD
      edge.head default = qH := by
    rw [List.getD_eq_getElem?_getD, hqH, Option.getD_some]
  rw [hheadD, hgetDT] at hleftC
  rw [hlastD, hgetDH] at hrightC
  have hcontA : nA.clusterPath.contains owner = true := by
    rw [hpT] at hleftC
    exact List.contains_iff_mem.mpr hleftC
  have hcontB : nB.clusterPath.contains owner = true := by
    rw [hpH] at hrightC
    exact List.contains_iff_mem.mpr hrightC
  exact ⟨index, edge, hedge, hne, htailLt, hheadLt, hleC1, hleC2,
    nA, nB, hnA, hnB, hcontA, hcontB⟩
/-- Exact dummy-only restriction of the group-top closure. Exact counterpart of
`GroupTopDummyRankLe`. -/
def X_GroupTopDummyRankLe : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions} {exact : List Nat},
    componentRunX P exact
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    v < (componentCandidate graph comp candidate).nodes.length →
    ∀ {i : Nat}, i < run.proper.nodes.length →
    (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
    (run.proper.nodes.getD i default).dummy = true →
    rk run.proper.rank v ≤ rk run.proper.rank i

/-- Exact dummy restriction via the lower chain endpoint. Replay of
`groupTopDummyRankLe`. -/
theorem X_groupTopDummyRankLe : X_GroupTopDummyRankLe := by
  intro P inp o exactIds lines graph0 graph measured h0 h hlines hwf hfp
    comp hcomp candidate run labels orderOptions exact hrun v nd hvGet hbordV hvcg
    i hi hpath hdum
  have howner : nd.decl ∈ (run.proper.nodes.getD i default).node.clusterPath :=
    List.contains_iff_mem.mp hpath
  obtain ⟨index, edge, _, _, htailLt, _, hle1, _, nA, _, hnA, _, hcontA, _⟩ :=
    X_dummy_chain_bracket hrun hi hdum howner
  obtain ⟨rr, hrr, hclose⟩ :=
    X_GroupTopSubtreeRankCg_holds h0 h hlines hwf hfp hcomp hrun hvGet hbordV
  have hgetDA : (componentCandidate graph comp candidate).nodes.getD edge.tail default = nA := by
    simp [List.getD_eq_getElem?_getD, hnA]
  have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD edge.tail
      default).clusterPath.contains nd.decl = true := by
    rw [hgetDA]; exact hcontA
  have hleTail : rk rr.ranks v ≤ rk rr.ranks edge.tail :=
    hclose edge.tail htailLt hgetDContains
  obtain ⟨rrS, _, hrrS, hcS, _, hranksS, _, _⟩ :=
    X_rankSource_of_componentRun h0 h hcomp hrun
  have hrrEq : rr = rrS := Except.ok.inj (hrr.symm.trans hrrS)
  subst hrrEq
  have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := X_prepared_coordinate_original_rk (P := P) (exact := exact) hrr hranksS hvcg
    rw [← hcS]; exact h1
  have hTcoord : rk run.coordinateProper.rank edge.tail = rk rr.ranks edge.tail := by
    have h1 := X_prepared_coordinate_original_rk (P := P) (exact := exact) hrr hranksS htailLt
    rw [← hcS]; exact h1
  have erv : rk run.proper.rank v = rk run.coordinateProper.rank v :=
    X_proper_rank_eq_local hrun v
  have eri : rk run.proper.rank i = rk run.coordinateProper.rank i :=
    X_proper_rank_eq_local hrun i
  omega

/-- Exact executed rank bound for derived proper nodes. Exact counterpart of
`ProperDerivedRank`. -/
def X_ProperDerivedRank : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options} {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions} {exact : List Nat},
    componentRunX P exact
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    v < (componentCandidate graph comp candidate).nodes.length →
    ∀ {i : Nat}, i < run.proper.nodes.length →
    (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
    ((run.proper.nodes.getD i default).dummy = true ∨
      (run.proper.nodes.getD i default).node.border = -1 ∨
      (run.proper.nodes.getD i default).node.border = 1 ∨
      (run.proper.nodes.getD i default).node.border = 3) →
    rk run.proper.rank v ≤ rk run.proper.rank i

/-- Exact derived closure from its seams. Replay of
`properDerivedRank_of_seams`. -/
theorem X_properDerivedRank_of_seams (hcg : X_GroupTopSubtreeRankCg)
    (hdummy : X_GroupTopDummyRankLe) : X_ProperDerivedRank := by
  intro P inp o exactIds lines graph0 graph measured h0 h hlines hwf hfp
    comp hcomp candidate run labels orderOptions exact hrun
    v nd hnode hborder hvcg i hi hpath hkind
  rcases hkind with hd | hb1 | hb2 | hb3
  · exact hdummy h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath hd
  · exact X_side_rank_ge hcg h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg
      hi hpath (Or.inl hb1)
  · exact X_side_rank_ge hcg h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg
      hi hpath (Or.inr hb2)
  · exact X_title_rank_ge hcg h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg
      hi hpath hb3

/-- Exact derived closure with the dummy residual as hypothesis. -/
theorem X_properDerivedRank (hdummy : X_GroupTopDummyRankLe) : X_ProperDerivedRank :=
  X_properDerivedRank_of_seams X_GroupTopSubtreeRankCg_holds hdummy

/-- The exact executed rank closure from its two seams. Replay of
`groupTopSubtreeRankProper_of_seams`. -/
theorem X_topRank_of_seams (hcg : X_GroupTopSubtreeRankCg)
    (hder : X_ProperDerivedRank) {exactIds : List String} : X_TopRank exactIds := by
  intro P inp o lines graph0 graph measured h0 h hlines hwf hfp
    comp hcomp candidate run labels orderOptions hrun v nd hnode hborder hvcg i hi hpath
  obtain ⟨rr, labeled, hrr, hcoord, hkeys, hranks, _, _⟩ :=
    X_rankSource_of_componentRun h0 h hcomp hrun
  obtain ⟨rr2, hrr2, hclose⟩ := hcg h0 h hlines hwf hfp hcomp hrun hnode hborder
  have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
  subst hrrEq
  have erv : rk run.proper.rank v = rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank v := by
    rw [X_proper_rank_eq_local hrun v, hcoord]
  have eri : rk run.proper.rank i = rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank i := by
    rw [X_proper_rank_eq_local hrun i, hcoord]
  rw [erv, eri]
  have hpi : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  obtain ⟨cn, hcn, hcdum, hcbord, hcpath⟩ := X_proper_coord_record hrun hpi
  have hcpath' : cn.node.clusterPath.contains nd.decl = true := by
    have h := hpath
    rwa [← hcpath] at h
  have hci : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[i]? = some cn := by
    rw [hcoord]; exact hcn
  rcases X_coordinateGraph_lookupX P (exactDecls exactIds inp) labeled hci with
    ⟨m, hm, hdm, _, hpm, _⟩ | ⟨_, hside⟩ | ⟨_, _, _, _, _, qb3, _⟩
  · by_cases hmD : m.dummy = false
    · rcases hkeys i m hm with ⟨n, hn, _, _, hnp⟩ | ⟨hdT, _, _⟩
      · have hnlt : i < (componentCandidate graph comp candidate).nodes.length :=
          (List.getElem?_eq_some_iff.mp hn).1
        have hgetD : (componentCandidate graph comp candidate).nodes.getD i default =
            n := by
          rw [List.getD_eq_getElem?_getD, hn, Option.getD_some]
        have hnpath : ((componentCandidate graph comp candidate).nodes.getD i
            default).clusterPath.contains nd.decl = true := by
          rw [hgetD, ← hnp, ← hpm hmD]
          exact hcpath'
        have hrv : rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank v = rk rr.ranks v :=
          X_prepared_coordinate_original_rk hrr hranks hvcg
        have hri : rk (coordinateGraphX P (exactDecls exactIds inp) labeled).rank i = rk rr.ranks i :=
          X_prepared_coordinate_original_rk hrr hranks hnlt
        rw [hrv, hri]
        exact hclose i hnlt hnpath
      · simp [hmD] at hdT
    · have hmT : m.dummy = true := by
        cases hmd : m.dummy with
        | true => rfl
        | false => exact (hmD hmd).elim
      have hpnD : (run.proper.nodes.getD i default).dummy = true := by
        rw [← hcdum, hdm]
        exact hmT
      rw [← erv, ← eri]
      exact hder h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
        (Or.inl hpnD)
  · rcases hside with hs | hs
    · rw [← erv, ← eri]
      exact hder h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
        (Or.inr (Or.inl (by rw [← hcbord]; exact hs)))
    · rw [← erv, ← eri]
      exact hder h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
        (Or.inr (Or.inr (Or.inl (by rw [← hcbord]; exact hs))))
  · rw [← erv, ← eri]
    exact hder h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
      (Or.inr (Or.inr (Or.inr (by rw [← hcbord]; exact qb3))))

/-- Exact top rank holds for executed exact layouts. -/
theorem x_topRank_holds (exactIds : List String) : X_TopRank exactIds := by
  intro P inp o lines graph0 graph measured h0 h hlines hwf hfp
    comp hcomp candidate run labels orderOptions hrun v nd hnode hborder hvcg i hi hpath
  exact X_topRank_of_seams X_GroupTopSubtreeRankCg_holds
    (X_properDerivedRank X_groupTopDummyRankLe)
    h0 h hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath
end PipelineImpl
end Layered
end Elegant
