import Elegant.Layered.RunStageChainKeys
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.FrameClearanceFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/- Probe summary (proofs/wip/Probe/PartPlainNodeProbe.lean, executed layouts):
- emptyToPlain (empty group G with route G to a): routed part comp [0,1,2]
  has a plain candidate node (nplain 1). hplain holds here.
- emptySelf (empty group G with self-loop G to G): routed part comp [0,2]
  (top G plus bottom G) has nplain 0, ntop 1, nbot 1, routes 1.
  No border-0 candidate node exists, so the hplain premise of
  partPositiveContent is FALSE. Witness is this input and part.
- twoEmpty (two empty groups G to H): routed part comp [0,1,2,3]
  has nplain 0, routes 1. Again no plain candidate node: hplain FALSE.
- control (plain a to b): plain holds.
Detail probe (PartPlainDetailProbe.lean): both counterexamples still have a
positive group-top frame and distinct route y values:
- emptySelf part [0,2]: v 0 top frame w 5280 h 6144 both positive;
  route ys [0,0,1536,1536] has distinct y.
- twoEmpty part: tops (3744,5376), (3740,5376) both positive;
  route ys [5376,8448] distinct.
Hence the weakest true replacement keeps positivity but allows group tops.
The three targets are AliasDeclTransport (proved below as aliasDeclTransport),
FrameRectPositive (universal form for arbitrary cg remains open; the executed
existential replacement PartFrameWitness is proved to imply
PartPositiveContent), and the hplain premise of partPositiveContent (FALSE by
the emptySelf/twoEmpty witnesses above; replaced by PartFrameWitness). -/

/-- Weakest true replacement for the false `hplain` premise: every routed part
has a plain-or-group-top candidate node whose executed frame rect is positive
in both axes. This is about one construction phase (`componentRun`/`frameRect`
on the component candidate), strictly simpler than `PartPositiveContent`
(which is about placed part rects and route point spans). Probe: 4/4 routed
parts in `PartPlainNodeProbe` satisfy it (plain case for `emptyToPlain` and
`control`; group-top case `v=0` for `emptySelf` and `twoEmpty` with the
`PartPlainDetailProbe` dimensions above). -/
def PartFrameWitness (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ {part : List Nat × Part}, part ∈ execution.componentsAcc.parts →
      part.1 = comp → part.2.routes ≠ [] →
      ∃ (v : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node ∧
        (node.border = 0 ∨ node.border = -2) ∧
        0 < (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run v).w ∧
        0 < (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run v).h

/-- Rect lookup in a placed component (copy of the private
`RunStageChainKeys.placeComponent_rects_get_aux`, which cannot be imported;
uses only `Pipeline`). -/
theorem placeComponent_rects_get_copy (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponent P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
        (0 - (placeBounds P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponent placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- `PartPositiveContent` from the witness: the witness node supplies a shifted
frame rect positive in both axes, so the width conjunct and the left
(height) disjunct both hold; the route `y`-span alternative is not needed. -/
theorem partPositiveContent_of_witness {inp : Input} {o : Options}
    {res : FamilyResult} (hwit : PartFrameWitness inp o res) :
    PartPositiveContent inp o res := by
  intro execution part hpart hroutes
  obtain ⟨index, run, loops, _area, hcomp, hrun, heq⟩ :=
    execution_part_run execution hpart
  obtain ⟨v, _node, hnode, _hbord, hposW, hposH⟩ :=
    hwit execution part.1 index run hcomp hrun hpart rfl hroutes
  have hrectsEq : part.2.rects =
      (placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0
        execution.measured loops).rects := by rw [heq]
  have hi : v < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hget := placeComponent_rects_get_copy execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured loops hi
  have hmem : shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v) ∈
      part.2.rects := by
    rw [hrectsEq]
    exact List.mem_of_getElem? hget
  have hw : 0 < (shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v)).w := hposW
  have hh : 0 < (shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v)).h := hposH
  exact ⟨⟨_, hmem, hw⟩, Or.inl ⟨_, hmem, hh⟩⟩

-- Copies of the private GroupAnchors counting and bottom-node lemmas, renamed
-- as required (private lemmas of other files cannot be imported).

private theorem alias_countP_take_add_one {α : Type} (p : α → Bool)
    {l : List α} {i n : Nat} (hn : n ≠ 0) (hi : i < l.length) (hpi : p l[i] = true) :
    (l.take i).countP p + 1 ≤ (l.take (i + n)).countP p := by
  have hsplit : (l.take (i + n)).countP p =
      (l.take i).countP p + ((l.drop i).take n).countP p := by
    rw [List.take_add, List.countP_append]
  rw [hsplit]
  have hwindow : l[i] ∈ (l.drop i).take n := by
    have h1 : (l.drop i)[0]? = some l[i] := by
      rw [List.getElem?_drop, Nat.add_zero]
      exact List.getElem?_eq_getElem hi
    have h2 : ((l.drop i).take n)[0]? = (l.drop i)[0]? := by
      rw [List.getElem?_take]
      simp [Nat.pos_of_ne_zero hn]
    have h0 : ((l.drop i).take n)[0]? = some l[i] := by rw [h2, h1]
    exact List.mem_of_getElem? h0
  have hge : 1 ≤ (((l.drop i).take n).filter p).length := by
    have hmem : p l[i] = true := hpi
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hwindow, hmem⟩
  simp only [List.countP_eq_length_filter]
  omega

private def aliasBottomNodesOf (full sub : List ModelBox) (off : Nat) : List Node :=
  (sub.zipIdx off).filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0
        clusterPath := Compound.path full q.1 ++ [q.2], border := 2 }
    else none

private theorem aliasBottomNodesOf_getElem?_decl {full sub : List ModelBox} {off k : Nat}
    {x : Node} (hx : (aliasBottomNodesOf full sub off)[k]? = some x) :
    ∃ d g, sub[d]? = some g ∧ g.role = .group ∧ x.decl = d + off ∧
      ((sub.take d).filter fun b => b.role == .group).length = k := by
  induction sub generalizing off k with
  | nil => simp [aliasBottomNodesOf] at hx
  | cons b bs ih =>
    unfold aliasBottomNodesOf at hx
    rw [List.zipIdx_cons] at hx
    by_cases hb : b.role = .group
    · have hbeq : (b.role == .group) = true := beq_iff_eq.mpr hb
      simp only [hbeq, ↓reduceIte, List.filterMap_cons] at hx
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨0, b, List.getElem?_cons_zero, hb, by simp, by simp⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
        refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
        · simpa using hdg
        · have : d + 1 + off = d + (off + 1) := by omega
          rw [this]; exact hdecl
        · have htake : ((b :: bs).take (d + 1)).filter
              (fun b => b.role == .group) =
            b :: (bs.take d).filter (fun b => b.role == .group) := by
            rw [List.take_succ_cons]
            simp [hb]
          rw [htake, List.length_cons, hcount]
    · have hbf : (b.role == .group) = false := by
        cases hz : (b.role == .group) with
        | true => exact absurd (beq_iff_eq.mp hz) hb
        | false => rfl
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons] at hx
      obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
      refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
      · simpa using hdg
      · have : d + 1 + off = d + (off + 1) := by omega
        rw [this]; exact hdecl
      · have htake : ((b :: bs).take (d + 1)).filter
              (fun b => b.role == .group) =
          (bs.take d).filter (fun b => b.role == .group) := by
          rw [List.take_succ_cons]
          have hbf2 : (b.role == .group) = false := hbf
          simp only [hbf2, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
        rw [htake, hcount]

private theorem alias_bottom_node_decl {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes : List Node} (hlen : nodes.length = boxes.length)
    {i j : Nat} {x : Node} {b : ModelBox}
    (hj : j = boxes.length + ((boxes.take i).filter fun b => b.role == .group).length)
    (hx : (Compound.markNodes boxes pad titles nodes)[j]? = some x)
    (hbi : boxes[i]? = some b) (hb : b.role = .group) :
    x.decl = i := by
  rw [markNodes_eq] at hx
  have htopLen : (nodes.zipIdx.map (markOne boxes pad titles)).length = nodes.length := by
    simp [List.length_map, List.length_zipIdx]
  have hjge : (nodes.zipIdx.map (markOne boxes pad titles)).length ≤ j := by
    rw [htopLen, hlen]; omega
  rw [List.getElem?_append_right hjge] at hx
  have hk : j - (nodes.zipIdx.map (markOne boxes pad titles)).length =
      ((boxes.take i).filter fun b => b.role == .group).length := by omega
  rw [hk] at hx
  have hme : markExtras boxes = aliasBottomNodesOf boxes boxes 0 := rfl
  rw [hme] at hx
  obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := aliasBottomNodesOf_getElem?_decl hx
  have hi : i < boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hcntI : ((boxes.take i).filter fun b => b.role == .group).length =
      j - (nodes.zipIdx.map (markOne boxes pad titles)).length := by omega
  have hidi : i = d := by
    rcases Nat.lt_trichotomy i d with hlt | heq | hgt
    · have hbdi : (fun b => b.role == .group) b = true := beq_iff_eq.mpr hb
      have hmono := alias_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := i) (n := d - i) (Nat.sub_ne_zero_of_lt hlt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hbi
          rw [heq]; exact hbdi)
      have hrewrite : i + (d - i) = d := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
    · exact heq
    · have hdi : d < boxes.length := (List.getElem?_eq_some_iff.mp hdg).1
      have hgid : (fun b => b.role == .group) g = true := beq_iff_eq.mpr hgg
      have hmono := alias_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := d) (n := i - d) (Nat.sub_ne_zero_of_lt hgt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hdg
          rw [heq]; exact hgid)
      have hrewrite : d + (i - d) = i := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
  subst hidi
  simpa using hdecl

private theorem alias_endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases hbj : boxes[j]? with
    | none => exact Or.inl rfl
    | some target =>
      dsimp only
      by_cases hc : (box.role != .group || i == j) = true
      · rw [ite_eq_left hc]
        exact Or.inl rfl
      · rw [ite_eq_right hc]
        by_cases hd : (s == Compound.inside boxes box.id target.id) = true
        · rw [ite_eq_left hd]
          exact Or.inl rfl
        · rw [ite_eq_right hd]
          refine Or.inr ⟨rfl, ?_⟩
          intro box' hb'
          have heq : box' = box := (Option.some.inj hb').symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl

private theorem alias_pos_decl {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (s : Bool)
    {pos other : Nat} {src tgt : ModelBox}
    (hsrc : inp.boxes[pos]? = some src)
    (_htgt : inp.boxes[other]? = some tgt)
    {a : Nat}
    (ha : a = Compound.endpoint
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) s pos other)
    {node : Node} (hnode : execution.graph.nodes[a]? = some node) :
    node.decl = pos := by
  obtain ⟨nodes0, _edges0, titles, hprepared, hlen_nodes, _hmeta⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
          (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hprep_len : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).length = inp.boxes.length := by
    simp
  have hlen0 : nodes0.length =
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).length := by
    rw [hlen_nodes, hlines, hprep_len]
  have hbp : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[pos]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src) := by
    rw [List.getElem?_map, hsrc]
    simp
  rcases alias_endpoint_cases (boxes := (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)) s pos other with h | ⟨hbot, hgroup⟩
  · have haPos : a = pos := ha.trans h
    subst haPos
    by_cases hpbG : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        ({ src with role := .node } : ModelBox) else src).role = .group
    · have hfixedFalse : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false := by
        cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
        | true =>
          simp only [hf, ↓reduceIte] at hpbG
          exact absurd hpbG (by intro hcon; cases hcon)
        | false => rfl
      have hsrcGroup : src.role = .group := by
        rw [hfixedFalse] at hpbG hbp
        simpa using hpbG
      obtain ⟨node', hn', _hbord, hdecl⟩ :=
        execution.nonfixed_group_graph_node hsrc hsrcGroup hfixedFalse
      have heq : node = node' := Option.some.inj (hnode.symm.trans hn')
      rw [heq]
      exact hdecl
    · have hplain : ¬ (src.role = .group ∧
          inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false) := by
        intro ⟨hr, hf⟩
        simp [hf, hr] at hpbG
      obtain ⟨node', hn', _hbord, _hpath, hdecl⟩ :=
        execution.plain_graph_node hsrc hplain
      have heq : node = node' := Option.some.inj (hnode.symm.trans hn')
      rw [heq]
      exact hdecl
  · have haBot : a = Compound.bottomIndex
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) pos := ha.trans hbot
    have hpbG : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        ({ src with role := .node } : ModelBox) else src).role = .group := by
      have hb := hgroup _ hbp
      simpa using hb
    have hnodes : execution.graph.nodes = Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
        execution.params.clusterPad titles nodes0 := by
      rw [hprepared]; rfl
    have hx : (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)
        execution.params.clusterPad titles nodes0)[a]? = some node := by
      rw [← hnodes]
      exact hnode
    have hj : a = (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box).length +
        (((inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box).take pos).filter
          fun b => b.role == .group).length := by
      rw [haBot]; rfl
    exact alias_bottom_node_decl hlen0 hj hx hbp hpbG

/-- Group-alias declaration transport through the run stages: an aliased
endpoint's graph node carries a model endpoint declaration. -/
theorem aliasDeclTransport {inp : Input} {o : Options} {res : FamilyResult} :
    AliasDeclTransport inp o res := by
  intro execution index route raw hroute hraw a node ha hnode
  obtain ⟨_hdecl, _hrev, src, tgt, hsrc, _hsrcId, htgt, _htgtId⟩ :=
    edgeOf_semantic_endpoints hraw
  rcases ha with haT | haH
  · have htail : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail =
        Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) true raw.tail raw.head := rfl
    have haTail : a = Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) true raw.tail raw.head := by
      rw [haT, htail]
    have hdeclEq := alias_pos_decl execution true hsrc htgt haTail hnode
    exact Or.inl hdeclEq
  · have hhead : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head =
        Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) false raw.head raw.tail := rfl
    have haHead : a = Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) false raw.head raw.tail := by
      rw [haH, hhead]
    have hdeclEq := alias_pos_decl execution false htgt hsrc haHead hnode
    exact Or.inr hdeclEq

/-- Closed corollary in the exact shape `flatC6_closed` takes: no residual
hypothesis remains for the key transport. -/
theorem properChainEndpointKeys' (inp : Input) (o : Options) (res : FamilyResult)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true) :
    ProperChainEndpointKeys inp o res :=
  properChainEndpointKeys aliasDeclTransport

/-- Closed corollary in the exact shape `flatC6_closed` takes: the frame
witness residual remains as an explicit premise. -/
theorem partPositiveContent' (inp : Input) (o : Options) (res : FamilyResult)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (hwit : PartFrameWitness inp o res) :
    PartPositiveContent inp o res :=
  partPositiveContent_of_witness hwit

end PipelineImpl
end Layered
end Elegant
