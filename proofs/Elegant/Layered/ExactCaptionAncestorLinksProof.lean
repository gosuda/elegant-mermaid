import Elegant.Layered.ExactCaptionAncestorsProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ForeignBorderSpansProof

set_option autoImplicit false

namespace Elegant
namespace Layered
open CoordsImpl
namespace PipelineImpl

/-- The shared execution prefix needed by exact component frame proofs. -/
structure ExactFramePrefix (exactIds : List String) (inp : Input) (o : Options) where
  params : Params
  lines : List (List Measure.Line)
  measured : List MeasuredLabel
  graph0 : Graph
  graph : Graph
  checked : checkedParams o.profile inp.kind = .ok params
  lines_length : lines.length = inp.boxes.length
  graph0_eq : measuredGraph params inp o lines = .ok graph0
  graph_eq : exactGraph params exactIds inp o measured graph0 = .ok graph

def SceneExecutionX.exactFramePrefix {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    ExactFramePrefix exactIds inp o where
  params := execution.params
  lines := execution.lines
  measured := execution.measured
  graph0 := execution.graph0
  graph := execution.graph
  checked := execution.checked
  lines_length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  graph0_eq := execution.graph0_eq
  graph_eq := execution.graph_eq

/-- W-form (execution, local admission) of the group-link left residual
`XCA_LinkLeftX`: the direct parent group frame starts strictly left of its
direct child group frame over one executed exact run. -/
def XCA_LinkLeftXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {parentIndex childIndex : Nat} {parent child : Node}
      {parentBox childBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent →
    parent.border = -2 →
    (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child →
    child.border = -2 →
    inp.boxes[parent.decl]? = some parentBox →
    inp.boxes[child.decl]? = some childBox →
    childBox.parent = parentBox.id → childBox.parent ≠ "" →
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).x <
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).x

/-- W-form (execution, local admission) of the group-link right residual
`XCA_LinkRightX`: the direct child group frame ends strictly left of its
direct parent group frame right edge over one executed exact run. -/
def XCA_LinkRightXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {parentIndex childIndex : Nat} {parent child : Node}
      {parentBox childBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent →
    parent.border = -2 →
    (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child →
    child.border = -2 →
    inp.boxes[parent.decl]? = some parentBox →
    inp.boxes[child.decl]? = some childBox →
    childBox.parent = parentBox.id → childBox.parent ≠ "" →
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).w <
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).x +
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).w

/-- W-form (execution, local admission) of the group-link top residual
`XCA_LinkTopX`. Residual reason: left
unproved because vertical strictness needs the exact rank-strictness chain
(child-top rank vs ancestor bottom rank) with no exact replay yet; tracked
probe `ExactCaptionAncestorFactsTProbe` shows zero top violations on flat,
nested, fixed, and wide inputs. -/
def XCA_LinkTopXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {parentIndex childIndex : Nat} {parent child : Node}
      {parentBox childBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent →
    parent.border = -2 →
    (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child →
    child.border = -2 →
    inp.boxes[parent.decl]? = some parentBox →
    inp.boxes[child.decl]? = some childBox →
    childBox.parent = parentBox.id → childBox.parent ≠ "" →
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).y <
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).y

/-- W-form (execution, local admission) of the group-link bottom residual
`XCA_LinkBotX`. Residual reason: left
unproved because vertical strictness needs the exact child-bottom rank chain
with no exact replay yet; tracked probe `ExactCaptionAncestorFactsTProbe`
shows zero bottom violations on flat, nested, fixed, and wide inputs. -/
def XCA_LinkBotXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {parentIndex childIndex : Nat} {parent child : Node}
      {parentBox childBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent →
    parent.border = -2 →
    (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child →
    child.border = -2 →
    inp.boxes[parent.decl]? = some parentBox →
    inp.boxes[child.decl]? = some childBox →
    childBox.parent = parentBox.id → childBox.parent ≠ "" →
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex).h <
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).y +
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).h

/-- W-form (execution, local admission) of the group-link residual
`XCA_GroupLinkX`: the exact direct-parent link is strict on each side. -/
def XCA_GroupLinkXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {parentIndex childIndex : Nat} {parent child : Node}
      {parentBox childBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent →
    parent.border = -2 →
    (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child →
    child.border = -2 →
    inp.boxes[parent.decl]? = some parentBox →
    inp.boxes[child.decl]? = some childBox →
    childBox.parent = parentBox.id → childBox.parent ≠ "" →
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentIndex).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run childIndex)

/-- Group-link W-form from its four W sides: strict on each side, hence
strictly inside. -/
theorem XCA_groupLinkXW_holds (exactIds : List String)
    (hleft : XCA_LinkLeftXW exactIds)
    (hright : XCA_LinkRightXW exactIds)
    (htop : XCA_LinkTopXW exactIds)
    (hbot : XCA_LinkBotXW exactIds) :
    XCA_GroupLinkXW exactIds := by
  intro inp o res execution hwf hframed
  intro comp hcomp candidate run orderOptions hrun
  intro parentIndex childIndex parent child parentBox childBox
  intro hparent hpb hchild hcb hpbox hcbox href hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hleft execution hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne
  · exact hright execution hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne
  · exact htop execution hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne
  · exact hbot execution hwf hframed hcomp hrun hparent hpb hchild hcb hpbox hcbox href hne

private theorem xal_sized_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  unfold sizeProperPortsX
  simp

private theorem xal_coordinateGraph0_lookup (P : Params) (exact : List Nat)
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
  have hlen := xal_sized_length P exact p
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

private theorem xal_coordinateGraph_lookup (P : Params) (exact : List Nat)
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
  rcases xal_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
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

private theorem xal_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases xal_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]
private theorem xal_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
    ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ extra := by
  unfold titleReservations sizeProperPortsX
  exact ⟨_, rfl⟩

private theorem xal_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := xal_titled_rank_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

private theorem xal_titled_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := xal_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index

private theorem xal_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

private theorem xal_coordinate_rank_pair (P : Params) (exact : List Nat)
    (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
      rank)
    (hhi : rank ≤
      (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, xal_side_record hl rfl (Or.inl rfl),
    xal_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

private theorem xal_revKey {exactIds : List String} {inp : Input} {o : Options}
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

private theorem xal_groupPath {exactIds : List String} {inp : Input} {o : Options}
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

private theorem xal_cgShape {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactFramePrefix exactIds inp o) :
    CgShape execution.graph := by
  have hshape := measuredGraph_shape execution.graph0_eq
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    obtain ⟨na0, ha0, _, hb1, hp1⟩ := xal_revKey execution ha
    obtain ⟨nb0, hb0, _, hb2, hp2⟩ := xal_revKey execution hb
    exact hshape.1 a b na0 nb0 ha0 hb0 (by rw [hb1]; exact h1) (by rw [hb2]; exact h2)
      (by rw [hp1, hp2]; exact hp)
  · intro n hn
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, h0, _, hb, _⟩ := xal_revKey execution hv
    have h3 := hshape.2 n0 (List.mem_of_getElem? h0)
    rw [hb] at h3
    exact h3

private theorem xal_final_border_source {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.proper.nodes[index]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.coordinateProper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  obtain ⟨_, _, hlength, _, hrecords, hunchanged⟩ := proxyWidths_rel hproxy
  have hrouted : q0.nodes[index]? = some node := by
    rw [← hdrop] at hnode
    exact hnode
  have hbound : index < run.coordinateProper.nodes.length := by
    have hn := (List.getElem?_eq_some_iff.mp hrouted).1
    omega
  have hsource : run.coordinateProper.nodes[index]? =
      some run.coordinateProper.nodes[index] := List.getElem?_eq_getElem hbound
  obtain ⟨updated, hupdated, _, hborderEq, _⟩ := hrecords index _ hsource
  have hupdatedEq : updated = node := Option.some.inj (hupdated.symm.trans hrouted)
  have hsourceBorder : (run.coordinateProper.nodes[index]).node.border = node.node.border :=
    hborderEq.symm.trans (congrArg (fun value : ProperNode => value.node.border) hupdatedEq)
  have hnotProxy : ¬ ((run.coordinateProper.nodes[index]).node.border = -2 ∨
      (run.coordinateProper.nodes[index]).node.border = 2) := by
    rw [hsourceBorder]
    rcases hborder with hb | hb <;> omega
  obtain ⟨hexact, hx⟩ := hunchanged index _ hsource hnotProxy
  have heq : run.coordinateProper.nodes[index] = node :=
    Option.some.inj (hexact.symm.trans hrouted)
  refine ⟨hsource.trans (congrArg some heq), ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

private theorem xal_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

private theorem xal_bordersWellFormed {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX P exact labeled))) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready

private theorem xal_coordinate_side_rank_bounds {P : Params} {exact : List Nat}
    {source : Proper}
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX P exact source)))
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

private theorem xal_direct_group_path {exactIds : List String} {inp : Input}
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
  obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := xal_revKey execution hparentSource
  obtain ⟨_, _, hchildSource⟩ := componentCandidate_nonplain_source hchild (by omega)
  obtain ⟨child0, hchild0, hdC, hbC, hpC⟩ := xal_revKey execution hchildSource
  obtain ⟨parentOriginal, hparentOriginal, hparentDecl, hparentPath⟩ :=
    xal_groupPath execution hparent0 (hbP.trans hparentGroup)
  obtain ⟨childOriginal, hchildOriginal, hchildDecl, hchildPath⟩ :=
    xal_groupPath execution hchild0 (hbC.trans hchildGroup)
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

private theorem xal_group_bottom_bundle {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) = some bottom := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  obtain ⟨bottom, htitled, hbottom⟩ :=
    X_prepared_group_bottom execution.graph0_eq execution.graph_eq hcomp hrun hc hk
      hready hrecords hnode hgroup
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩

private theorem xal_group_side_rank_bounds {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some node.decl) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) = some bottom ∧
      side.node.clusterPath = node.clusterPath ∧
      0 ≤ rk run.coordinateProper.rank sideIndex ∧
      (rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index).toNat ≤
        (rk run.coordinateProper.rank sideIndex).toNat ∧
      (rk run.coordinateProper.rank sideIndex).toNat ≤
        (rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank bottom.2).toNat := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks,
    htitled, hbottom⟩ :=
    xal_group_bottom_bundle execution hcomp hrun hnode hgroup
  have hcoordinate : (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).nodes[sideIndex]? =
      some side := by
    rw [hc]
    exact hside
  obtain ⟨anchor, hanchor, generatedBottom, hfind, hpath, hnonneg, hlo, hhi⟩ :=
    xal_coordinate_side_rank_bounds hready hcoordinate hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := xal_revKey execution hgroupSource
  obtain ⟨box, hbox0, hdeclG, hpathG⟩ := xal_groupPath execution hgroup0 (hbG.trans hgroup)
  have hlast : node.clusterPath.getLast? = some node.decl := by
    rw [← hpG, hpathG]
    simp [← hdeclG, hdG]
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      (titleF ⟨node, false, none, false⟩).node.clusterPath.getLast? := by
    rw [← hpath, (titleF_keys _).2.2.1]
    exact howner.trans hlast.symm
  have htitledBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hindex := X_titled_group_owner_unique execution.graph0_eq execution.graph_eq
    hcomp hk hrecords hanchorLookup htitled hanchorBorder htitledBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[anchor.2]? =
      some (titleF ⟨node, false, none, false⟩) := by
    rw [hindex]
    exact htitled
  have hanchorEq : anchor.1 = titleF ⟨node, false, none, false⟩ :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  rw [hanchorEq, (titleF_keys _).2.2.1] at hfind hpath
  have hbottomEq : generatedBottom = bottom :=
    Option.some.inj (hfind.symm.trans hbottom)
  rw [hindex] at hlo
  rw [hbottomEq] at hhi
  rw [hc] at hnonneg hlo hhi
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks,
    htitled, hbottom, hpath, hnonneg, hlo, hhi⟩

private theorem xal_child_side_parent_borders {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank sideIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank sideIndex := by
  obtain ⟨rr, labeled, childBottom, hrr, hc, hk, hready, hrecords, hranks,
    _, hchildBottom, _, hnonneg, hlo, hhi⟩ :=
    xal_group_side_rank_bounds execution hcomp hrun hchild hchildGroup
      hside hsideBorder howner
  obtain ⟨parentBottom, hparentTitled, hparentBottom⟩ :=
    X_prepared_group_bottom execution.graph0_eq execution.graph_eq hcomp hrun hc hk
      hready hrecords hparent hparentGroup
  obtain ⟨parentOriginalBottom, hparentOriginalBottom, _, _, _, hparentFind⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq hk hrecords
      hparent hparentGroup hparentBottom
  obtain ⟨childOriginalBottom, hchildOriginalBottom, _, _, _, hchildFind⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq hk hrecords
      hchild hchildGroup hchildBottom
  have hpath := xal_direct_group_path execution hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hinterval := ranked_compound_child_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hparent) hparentGroup hparentFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr hchild) hchildGroup hpath hchildFind
  have hparentRank := xal_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hparent).1
  have hchildRank := xal_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hchild).1
  have hparentBottomRank := xal_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hparentOriginalBottom).1
  have hchildBottomRank := xal_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hchildOriginalBottom).1
  have htopBorder : (titleF ⟨parent, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hparentGroup
  have hbottomForTop :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨parent, false, none, false⟩).node.clusterPath) =
            some parentBottom := by
    simpa only [(titleF_keys _).2.2.1] using hparentBottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    xal_coordinate_rank_pair execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr hparentTitled) htopBorder hbottomForTop
      (rank := (rk run.coordinateProper.rank sideIndex).toNat)
      (by
        dsimp only at hinterval hparentRank hchildRank hparentBottomRank hchildBottomRank ⊢
        omega)
      (by
        dsimp only at hinterval hparentRank hchildRank hparentBottomRank hchildBottomRank ⊢
        omega)
  have hnatcast : ((rk run.coordinateProper.rank sideIndex).toNat : Int) =
      rk run.coordinateProper.rank sideIndex := by omega
  have hleftValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank left =
      rk run.coordinateProper.rank sideIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank right =
      rk run.coordinateProper.rank sideIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [hc] at hleft hright hleftValue hrightValue
  exact ⟨left, right, hleft, hright, hleftValue, hrightValue⟩

private theorem xal_child_side_parent_bracket {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
      ord.layers = run.layers ∧ side.dummy = false ∧
      side.node.clusterPath = child.clusterPath ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left sideIndex right := by
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    xal_child_side_parent_borders execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
  obtain ⟨_, _, _, _, hc, _, hready, _, _, _, _, hsidePath, _, _, _⟩ :=
    xal_group_side_rank_bounds execution hcomp hrun hchild hchildGroup
      hside hsideBorder howner
  have hdirect := xal_direct_group_path execution hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwformed := xal_bordersWellFormed hc hready
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
      have hz := hwformed.2.2 sideIndex side hside hd
      rcases hsideBorder with hb | hb <;> omega
  have hnonempty := hwformed.1 sideIndex side hside hsideBorder
  rw [hsidePath] at hnonempty
  have hpositive := List.length_pos_iff.mpr hnonempty
  have hpathNe : parent.clusterPath ≠ child.clusterPath := by
    intro heq
    have hlength := congrArg List.length hdirect
    rw [List.length_dropLast, heq] at hlength
    omega
  have hprefix : parent.clusterPath <+: side.node.clusterPath := by
    rw [hsidePath, ← hdirect]
    exact List.dropLast_prefix _
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨parent, false, none, false⟩, parentIndex)
        execution.params.clusterBorderW).node.clusterPath <+: side.node.clusterPath := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath <+: side.node.clusterPath
    rw [(titleF_keys _).2.2.1]
    exact hprefix
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper sideIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper sideIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hleftNe : left ≠ sideIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hside)
    have hp := congrArg (fun value : ProperNode => value.node.clusterPath) hn
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = side.node.clusterPath at hp
    rw [(titleF_keys _).2.2.1, hsidePath] at hp
    exact hpathNe hp
  have hrightNe : right ≠ sideIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hside)
    have hp := congrArg (fun value : ProperNode => value.node.clusterPath) hn
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = side.node.clusterPath at hp
    rw [(titleF_keys _).2.2.1, hsidePath] at hp
    exact hpathNe hp
  refine ⟨ord, left, right, horder, hlayers, hreal, hsidePath, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left sideIndex right _ side _ hleft hside hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

private theorem xal_strict_interval {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ left right : Nat,
      run.proper.nodes[sideIndex]? = some side ∧
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.proper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x <
        (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
      (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
          (Labels.rectAt run.proper run.xs run.ys sideIndex).w <
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
  obtain ⟨ord, left, right, _, hlayers, _, _, hleft, hright, hbracket⟩ :=
    xal_child_side_parent_bracket execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨_, labeled, _, hc, hk, _, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (xal_cgShape execution) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact xal_pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb)
      hba hbb hp
  have hsideNotTop : side.node.border ≠ -2 := by
    rcases hsideBorder with hb | hb <;> omega
  have hsideNotBottom : side.node.border ≠ 2 := by
    rcases hsideBorder with hb | hb <;> omega
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left sideIndex _ _ hlt hli hmi hleft hside
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    hsideNotTop hsideNotBottom
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri sideIndex right _ _ htr hmi hri hside hright
    hsideNotTop hsideNotBottom
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ := xal_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ := xal_border_record hrun hright (Or.inr rfl)
  obtain ⟨hsideFinal, hsideX⟩ := xal_border_record hrun hside hsideBorder
  have hsideWidth := (sizesNonneg_lookup hsizes sideIndex side hside).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
  have hsideLoops : 0 ≤ (side.node.loopExtent : Int) := Int.natCast_nonneg _
  have hparentLoops : 0 ≤ (parent.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
  refine ⟨left, right, hsideFinal, hleftFinal, hrightFinal, ?_, ?_⟩
  · simp only [coordSep, CoordsImpl.nodeW, hleft, hside, OrderImpl.borderLeft] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hsideFinal, hleftX, hsideX, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  · simp only [coordSep, CoordsImpl.nodeW, hside, hright, OrderImpl.borderRight,
      titleF, hparentGroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hsideFinal, hrightFinal, hsideX, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega

private theorem xal_side_horizontal_strict {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.proper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).x < (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
    (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
        (Labels.rectAt run.proper run.xs run.ys sideIndex).w <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).w := by
  have hcoordinate := (xal_final_border_source hrun hside hsideBorder).1
  obtain ⟨left, right, _, hleft, hright, hlo, hhi⟩ :=
    xal_strict_interval execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hcoordinate hsideBorder howner
  let cg := componentCandidate execution.graph comp candidate
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hframeGroup : (cg.nodes.getD parentIndex default).border = -2 := by
    rw [hparentGet]
    exact hparentGroup
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := xal_revKey execution hparentSource
  obtain ⟨box, _, hdeclP, hpathP⟩ := xal_groupPath execution hparent0 (hbP.trans hparentGroup)
  have hleftPath : (OrderImpl.borderLeft
      (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hparentGet]
    have hpg : parent.clusterPath = Compound.path inp.boxes box ++ [parent.decl] := by
      rw [← hpP, hpathP, ← hdeclP, hdP]
    simpa only [hparentGet] using hpg
  have hrightPath : (OrderImpl.borderRight
      (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    exact hleftPath
  have hleftContained := frameRect_side_marker_contained (P := execution.params)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
  show (frameRect execution.params cg run parentIndex).x <
      (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
    (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
        (Labels.rectAt run.proper run.xs run.ys sideIndex).w <
      (frameRect execution.params cg run parentIndex).x +
      (frameRect execution.params cg run parentIndex).w
  refine ⟨?_, ?_⟩
  · have h1' : (frameRect execution.params cg run parentIndex).x ≤
        (Labels.rectAt run.proper run.xs run.ys left).x := hleftContained.1
    have h2 := hlo
    omega
  · have h1 := hhi
    have h2' : (Labels.rectAt run.proper run.xs run.ys right).x +
        (Labels.rectAt run.proper run.xs run.ys right).w ≤
        (frameRect execution.params cg run parentIndex).x +
          (frameRect execution.params cg run parentIndex).w := hrightContained.2.1
    omega

private theorem xal_group_final_side {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (sideIndex : Nat) (side : ProperNode),
      run.proper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some node.decl := by
  obtain ⟨_, labeled, _, _, hc, _, _, hrecords, _, _, _⟩ :=
    xal_group_bottom_bundle execution hcomp hrun hnode hgroup
  let proxy := clearF (titleF ⟨node, false, none, false⟩)
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := xal_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpathG⟩ := xal_groupPath execution hgroup0 (hbG.trans hgroup)
  have hproxyLast : proxy.node.clusterPath.getLast? = some node.decl := by
    change (clearF (titleF ⟨node, false, none, false⟩)).node.clusterPath.getLast? = _
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1, ← hpG, hpathG]
    simp [← hdeclG, hdG]
  exact ⟨sideIndex, side, (xal_border_record hrun hside hsideBorder).1,
    hsideBorder, hsideOwner.trans (howner.symm.trans hproxyLast)⟩
private theorem xal_foldl_strict_minX (rects : List Rect) (b : Bounds) (lo : Int)
    (hb : lo < b.minX) (hall : ∀ r ∈ rects, lo < r.x) :
    lo < ((rects.foldl fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minX := by
  induction rects generalizing b with
  | nil => simpa using hb
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · show lo < min b.minX first.x
      have h1 := hb
      have h2 := hall first (by simp)
      omega
    · intro r hr
      exact hall r (List.mem_cons_of_mem _ hr)

private theorem xal_strict_minX_of_all_lt (rects : List Rect) (lo : Int)
    (hall : ∀ r ∈ rects, lo < r.x) (hne : rects ≠ []) :
    lo < (boundsOf rects []).minX := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    unfold boundsOf
    dsimp only
    exact xal_foldl_strict_minX _ _ _ (hall first (by simp)) hall

private theorem xal_foldl_strict_right (rects : List Rect) (b : Bounds) (hi : Int)
    (hb : b.right < hi) (hall : ∀ r ∈ rects, r.x + r.w < hi) :
    ((rects.foldl fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).right < hi := by
  induction rects generalizing b with
  | nil => simpa using hb
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · show max b.right (first.x + first.w) < hi
      have h1 := hb
      have h2 := hall first (by simp)
      omega
    · intro r hr
      exact hall r (List.mem_cons_of_mem _ hr)

private theorem xal_strict_right_of_all_lt (rects : List Rect) (hi : Int)
    (hall : ∀ r ∈ rects, r.x + r.w < hi) (hne : rects ≠ [])
    (hpos : 0 < hi) :
    (boundsOf rects []).right < hi := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    unfold boundsOf
    dsimp only
    exact xal_foldl_strict_right _ _ _ hpos hall

private theorem xal_centers_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ v : Nat, 0 ≤ run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨-, -, -, -, hcase⟩ := crossCoordsClusterWith_spec hcross
  rcases hcase with ⟨-, hxs⟩ | ⟨x0, x1, x2, x3, hpass, hxs⟩
  · rw [hxs]
    intro v
    simp
  · rw [hxs]
    unfold CoordsImpl.crossClusterPasses at hpass
    split at hpass
    · simp at hpass
    · next _ _ =>
      split at hpass
      · simp at hpass
      · dsimp only at hpass
        split at hpass
        · simp at hpass
        · next y0 h0 =>
          split at hpass
          · simp at hpass
          · next y1 h1 =>
            split at hpass
            · simp at hpass
            · next y2 h2 =>
              split at hpass
              · simp at hpass
              · next y3 h3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hpass
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hpass
                have hsz0 : y0.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h0).1
                have hsz1 : y1.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h1).1
                have hsz2 : y2.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h2).1
                have hsz3 : y3.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h3).1
                have hnn0 := (fbs_cluster_pass_nonneg h0).2
                have hnn1 := (fbs_cluster_pass_nonneg h1).2
                have hnn2 := (fbs_cluster_pass_nonneg h2).2
                have hnn3 := (fbs_cluster_pass_nonneg h3).2
                obtain ⟨o0, o1, o2, o3⟩ := fbs_balanceOffsets_nonneg y0 y1 y2 y3
                intro v
                by_cases hv : v < run.coordinateProper.nodes.length
                · rw [CoordsImpl.balanceValues_getD _ _ _ _ _ hv]
                  exact fbs_bal4_nonneg (by have := hnn0 v (by omega); omega)
                    (by have := hnn1 v (by omega); omega)
                    (by have := hnn2 v (by omega); omega)
                    (by have := hnn3 v (by omega); omega)
                · have hlen : (CoordsImpl.balanceValues run.coordinateProper.nodes.length y0 y1 y2
                        y3).length = run.coordinateProper.nodes.length := by
                    simp [CoordsImpl.balanceValues]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
                  exact Int.le_refl 0
private theorem xal_parent_right_pos {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
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
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run parentIndex).x +
      (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run parentIndex).w := by
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨sideIndex, side, hside, hsideBorder, howner⟩ :=
    xal_group_final_side execution hcomp hrun hchild hchildGroup
  have hcoordinate := (xal_final_border_source hrun hside hsideBorder).1
  obtain ⟨_ord, _left, right, _hord, _hlayers, _hdummy, _hpath, _hleft, hright, _hbracket⟩ :=
    xal_child_side_parent_bracket execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hcoordinate hsideBorder howner
  obtain ⟨hrightFinal, hrightX⟩ := xal_border_record hrun hright (Or.inr rfl)
  have hgroupGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hframeGroup : (cg.nodes.getD parentIndex default).border = -2 := by
    rw [hgroupGet]
    exact hparentGroup
  have hrightPath : (OrderImpl.borderRight (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes parentBox ++ [(cg.nodes.getD parentIndex default).decl] := by
    have hgroupPath : parent.clusterPath = Compound.path inp.boxes parentBox ++ [parent.decl] := by
      obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
      obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := xal_revKey execution hparentSource
      obtain ⟨box, hbox, hdeclP, hpathP⟩ := xal_groupPath execution hparent0 (hbP.trans hparentGroup)
      have hparentEq : box = parentBox := by
        rw [← hdeclP, hdP] at hbox
        exact Option.some.inj (hbox.symm.trans hparentBox)
      rw [← hpP, hpathP, ← hdeclP, hdP, hparentEq]
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hgroupGet]
    exact hgroupPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal) (Or.inr rfl) hrightPath
  have hmarker : (Labels.rectAt run.proper run.xs run.ys right).x +
      (Labels.rectAt run.proper run.xs run.ys right).w =
      run.xs.getD right 0 - Int.fdiv execution.params.clusterBorderW 2 +
        execution.params.clusterBorderW := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hrightFinal, OrderImpl.borderRight]
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have hxsNonneg := xal_centers_nonneg hrun right
  have h1 : (Labels.rectAt run.proper run.xs run.ys right).x +
      (Labels.rectAt run.proper run.xs run.ys right).w ≤
      (frameRect execution.params cg run parentIndex).x +
        (frameRect execution.params cg run parentIndex).w := hrightContained.2.1
  have h2 : 0 < (Labels.rectAt run.proper run.xs run.ys right).x +
      (Labels.rectAt run.proper run.xs run.ys right).w := by
    have e1 := hmarker
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at e1
    have e2 := hrightX
    omega
  show 0 < (frameRect execution.params cg run parentIndex).x +
    (frameRect execution.params cg run parentIndex).w
  omega


theorem exactGroupFrameStrict_horizontal {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
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
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).x <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).x ∧
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).w <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).w := by
  let cg := componentCandidate execution.graph comp candidate
  let parentFrame := frameRect execution.params cg run parentIndex
  let childFrame := frameRect execution.params cg run childIndex
  let borders := run.proper.nodes.zipIdx.filterMap fun entry =>
    if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
        entry.1.node.clusterPath.getLast? == some child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hchildGet : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  obtain ⟨sideIndex, side, hside, hsideBorder, howner⟩ :=
    xal_group_final_side execution hcomp hrun hchild hchildGroup
  have hmember : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
    rcases hsideBorder with hb | hb <;> simp [hb, howner]
  have hnonempty : borders ≠ [] := by
    intro hempty
    rw [hempty] at hmember
    exact List.not_mem_nil hmember
  have hall : ∀ rect ∈ borders,
      parentFrame.x < rect.x ∧ rect.x + rect.w < parentFrame.x + parentFrame.w := by
    intro rect hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcondition
      have hconditions := Bool.and_eq_true_iff.mp hcondition
      have hb : entry.1.node.border = -1 ∨ entry.1.node.border = 1 := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using hconditions.1
      have ho : entry.1.node.clusterPath.getLast? = some child.decl :=
        beq_iff_eq.mp hconditions.2
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      exact xal_side_horizontal_strict execution hwf hcomp hrun
        hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
        (List.mem_zipIdx_iff_getElem?.mp hentry) hb ho
    · cases heq
  have hmin : parentFrame.x < (boundsOf borders []).minX :=
    xal_strict_minX_of_all_lt _ _ (fun r hr => (hall r hr).1) hnonempty
  have hpos' : 0 < parentFrame.x + parentFrame.w :=
    xal_parent_right_pos execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hmax : (boundsOf borders []).right < parentFrame.x + parentFrame.w :=
    xal_strict_right_of_all_lt _ _ (fun r hr => (hall r hr).2) hnonempty hpos'
  have hchildX : childFrame.x = (boundsOf borders []).minX := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hchildRight : childFrame.x + childFrame.w = (boundsOf borders []).right := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf borders []).minX +
      ((boundsOf borders []).right - (boundsOf borders []).minX) = _
    omega
  show parentFrame.x < childFrame.x ∧
    childFrame.x + childFrame.w < parentFrame.x + parentFrame.w
  rw [hchildRight, hchildX]
  exact ⟨hmin, hmax⟩

theorem XCA_LinkLeftXW_holds (exactIds : List String) :
    XCA_LinkLeftXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro parentIndex childIndex parent child parentBox childBox
  intro hparent hpb hchild hcb hpbox hcbox href hne
  exact (exactGroupFrameStrict_horizontal execution.exactFramePrefix hwf hcomp hrun hparent hpb
    hchild hcb hpbox hcbox href hne).1

theorem XCA_LinkRightXW_holds (exactIds : List String) :
    XCA_LinkRightXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro parentIndex childIndex parent child parentBox childBox
  intro hparent hpb hchild hcb hpbox hcbox href hne
  exact (exactGroupFrameStrict_horizontal execution.exactFramePrefix hwf hcomp hrun hparent hpb
    hchild hcb hpbox hcbox href hne).2

end PipelineImpl


end Layered
end Elegant
