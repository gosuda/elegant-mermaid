import Elegant.Layered.SizingFacts
import Elegant.Layered.CgShape

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- `orientNode` swaps only `w`/`h`; `decl` is preserved once the direction
is a constructor. -/
private theorem orientNode_decl (d : Direction) (n : Node) :
    (orientNode d n).decl = n.decl := by
  cases d <;> rfl

/-- Ordinary non-fixed node metadata: the same `measuredGraph` execution that
`measuredGraph_node_text_fit` uses also produces a node record whose `border` is `0`.
`prepare` leaves the border of a `.node`-role record untouched, `orientNode` preserves
it, and `sizedNode` builds every node with the default border `0`. -/
theorem measuredGraph_node_border_zero
    {profile : Profile} {kind : String} {P : Params}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)} {g : Graph}
    (_hp : checkedParams profile kind = .ok P)
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box) (hrole : box.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false) :
    ∃ node, g.nodes[i]? = some node ∧ node.decl = i ∧ node.border = 0 := by
  have hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  unfold measuredGraph at hg
  obtain ⟨initial, hinitial, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, hnodes, hg⟩ := bind_ok hg
  have hgraph := Except.ok.inj hg
  subst g
  obtain ⟨_, hinit⟩ := mapM_getElem? _ _ _ hinitial
  obtain ⟨before, hsized, hbefore⟩ := hinit i (ls, i)
    (by simp only [List.getElem?_zipIdx, hline, Option.map_some, Nat.zero_add])
  unfold sizedNode at hsized
  obtain ⟨size, _, he⟩ := bind_ok' hsized
  have hb := Except.ok.inj he
  have hbefore_border : before.border = 0 := by rw [← hb]
  have hbefore_decl : before.decl = i := by rw [← hb]
  obtain ⟨_, hprocessed⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨after, hstep, hafter⟩ := hprocessed i (orientNode o.direction before, i)
    (by simp only [List.getElem?_zipIdx, List.getElem?_map, hbefore,
      Option.map_some, Nat.zero_add])
  have ha0 : after.border = 0 := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hstep
    simp [hfind, hbox, hrole] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        simpa only [hbefore_border] using orientNode_border o.direction before
  have hprepared := prepare_node_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) P.clusterPad
      (lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * P.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      { nodes := nodes, edges := edges, slot := P.slot }
      hafter (by simp only [List.getElem?_map, hbox, Option.map_some,
        hfixed, Bool.false_eq_true, ↓reduceIte]) hrole
  have hdecl : after.decl = i := by
    dsimp only at hstep
    simp only [bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at hstep
    simp [hfind, hbox, hrole] at hstep
    split at hstep
    · cases hstep
    · split at hstep
      · cases hstep
      · have he := Except.ok.inj hstep
        subst after
        rw [orientNode_decl]
        exact hbefore_decl
  exact ⟨_, hprepared, hdecl, ha0⟩

/-- Packed text fit for ordinary non-fixed `.node` inputs: under one successful
`SceneExecution`, every non-fixed node-role input whose measured text lines are
`lines[i]` satisfies the text-fit bounds of `measuredGraph_node_text_fit` and its
node's `w`/`h` are bounded by the oriented packed rectangle that `hcoverage`
assigns to the same key. `hcoverage` is the part-membership discharge owned by
the coverage worker; this theorem only consumes it. -/
theorem SceneExecution.ordinary_node_packed_text_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hcoverage : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i)
    {i : Nat} {ls : List Measure.Line} {box : ModelBox} {node : Node} {rect : Rect}
    (hline : execution.lines[i]? = some ls)
    (hbox : inp.boxes[i]? = some box) (hrole : box.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false)
    (hnode : execution.graph.nodes[i]? = some node)
    (hrect : execution.packedAcc.rects[i]? = some rect) :
    (ls.foldl (fun w line => max w line.width) 0) ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).w ∧
    ((ls.length : Int) * execution.params.lineH) ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).h := by
  obtain ⟨n0, hnode0, hdecl0, hb0⟩ := measuredGraph_node_border_zero
    execution.checked execution.graph_eq hline hbox hrole hfixed
  have hnode_eq : node = n0 := Option.some.inj (hnode.symm.trans hnode0)
  subst node
  obtain ⟨n1, hn1, _, hw, hh⟩ := measuredGraph_node_text_fit
    execution.checked execution.graph_eq hline hbox hrole hfixed
  have hn1_eq : n1 = n0 := Option.some.inj (hn1.symm.trans hnode0)
  subst n1
  have hfit := execution.packed_rect_minimum_dims_of_coverage hcoverage
    hnode0 hb0 hrect
  refine ⟨?_, ?_⟩
  all_goals
    cases hd : o.direction <;>
      simp only [hd, orientRect] at hw hh hfit ⊢ <;> omega


/-- Output box sizing for an ordinary non-fixed `.node` input: the scene box
produced by `box_index_origin` is the margin-shifted oriented packed
rectangle, and `ordinary_node_packed_text_fit` bounds the measured text
width/height by that rectangle's oriented dimensions. `hrect` is the
packed-rect existence owned by the coverage worker; node existence and border
are derived here. -/
theorem SceneExecution.ordinary_box_line_height_of_coverage
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hcoverage : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i)
    {index : Nat} {box : Box} (hbox : res.scene.boxes[index]? = some box)
    {source : ModelBox} (hsource : inp.boxes[index]? = some source)
    (hrole : source.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false)
    {ls : List Measure.Line} (hline : execution.lines[index]? = some ls)
    {rect : Rect} (hrect : execution.packedAcc.rects[index]? = some rect) :
    (ls.foldl (fun w line => max w line.width) 0) ≤ box.rect.w ∧
      ((ls.length : Int) * execution.params.lineH) ≤ box.rect.h := by
  obtain ⟨actual, hactual, hboxeq⟩ := execution.box_index_origin hbox
  rw [hsource] at hactual
  cases Option.some.inj hactual
  obtain ⟨n0, hnode0, _, _⟩ := measuredGraph_node_border_zero
    execution.checked execution.graph_eq hline hsource hrole hfixed
  have hfit := execution.ordinary_node_packed_text_fit
    hcoverage hline hsource hrole hfixed hnode0 hrect
  have hget : execution.packedAcc.rects.getD index default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hi] using heq
  rw [hboxeq, hget]
  dsimp only [shiftRect]
  exact ⟨by omega, by omega⟩
end PipelineImpl
end Layered
end Elegant
