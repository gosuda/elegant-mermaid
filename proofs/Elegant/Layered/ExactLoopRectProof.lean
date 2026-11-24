import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.LoopRectCrossPartProof
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactBorder2UnchangedProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact twins of the plain loop-rectangle facts consumed by `flatC6_closed`.

Plain sources: `LoopRectPlainSourceProof.lean` (`LoopRectTopReal`,
`LoopRectFixedReal`, `LoopRectBottomReal`, `LoopRectRangeDegReal`) closed in
`LoopRectRealClosed.lean` (`loopRectBottomReal_holds`,
`loopRectRangeDegReal_holds`, `loopRectFixedReal_holds`) and
`LoopRectResidualsProof.lean` (`loopRectTopReal_closed` modulo `hx`).
Each `XL_` definition below replays the plain shape over `SceneExecutionX`
with `componentRunX` / `placeComponentExact` / `placeBoundsX`.
-/

/-- Exact twin of `LoopRectBottomReal`. -/
def XL_LoopRectBottomReal (exactIds : List String) (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = 2 →
      False

/-- Exact twin of `LoopRectRangeDegReal`. -/
def XL_LoopRectRangeDegReal (exactIds : List String) (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = none →
    run.proper.nodes[v]? = none →
    False

/-- Exact twin of `LoopRectFixedReal`. -/
def XL_LoopRectFixedReal (exactIds : List String) (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node} {key : Nat} {src : ModelBox},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = 0 →
      q.1.1[v]? = some key → inp.boxes[key]? = some src →
      inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = true →
      ∃ (key' : Nat) (src' : ModelBox),
        q.1.1[v]? = some key' ∧ inp.boxes[key']? = some src' ∧ src'.role ≠ .group

/-- Exact twin of `LoopRectTopForeignReal` (the plain `hx` premise). -/
def XL_LoopRectTopForeignReal (exactIds : List String) (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = -2 →
      ∀ {w : Nat} {key : Nat} {member : Node},
        q.1.1[w]? = some key →
        ((componentCandidate execution.graph q.1.1 candidate).nodes.getD w default).border = 0 →
        (componentCandidate execution.graph q.1.1 candidate).nodes[w]? = some member →
        member.border = 0 →
        member.clusterPath.contains node.decl = false →
        frameRect execution.params (componentCandidate execution.graph q.1.1 candidate) run w =
          frameRect execution.params
            (componentCandidate execution.graph q.1.1 candidate) run v →
        False

/-- Exact twin of `LoopRectTopReal`. -/
def XL_LoopRectTopReal (exactIds : List String) (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = -2 →
      False

/-- Closed exact range-degenerate case: pure run geometry, no exact seam. -/
theorem XL_loopRectRangeDegReal_holds {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult} :
    XL_LoopRectRangeDegReal exactIds inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect hn hp
  have hdeg := loopRect_rangeDeg_frame (P := execution.params)
    (cg := componentCandidate execution.graph q.1.1 candidate) (run := run)
    (v := v) hn hp
  have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
  have hw0 : (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v).w = 0 :=
    congrArg Rect.w hdeg
  have hh0 : (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v).h = 0 :=
    congrArg Rect.h hdeg
  omega

/-- Exact bottom-marker frame is flat: height `0` through the exact run. -/
private theorem xl_bottomFrameHeight {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {w : Nat} {wNode : Node} (hw : cg.nodes[w]? = some wNode)
    (hbottom : wNode.border = 2) :
    (frameRect P cg run w).h ≤ 0 := by
  obtain ⟨_ranks, _p0, labeled, q0, hn, hlabeled, hc, _hord, _hxs,
    hproxy, hdrop, _hr, _hroutes⟩ := componentRunX_spec hrun
  obtain ⟨_edges, _rank, _nlen, _xlen, hrecords, _nonproxy⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hlabRec : labeled.nodes[w]? = some (⟨wNode, false, none, false⟩ : ProperNode) :=
    addLabelNodes_untouched_node hlabeled (normalize_node_record hn hw) rfl
  have hdummyW : (⟨wNode, false, none, false⟩ : ProperNode).dummy = false := rfl
  have hcpRec : (coordinateGraphX P exact labeled).nodes[w]? =
      some (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))) :=
    X_coordinateGraph_marker_record hlabRec (Or.inr hbottom) hdummyW
  have hrunCpRec : run.coordinateProper.nodes[w]? =
      some (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))) := by
    rw [← hc]; exact hcpRec
  obtain ⟨final, hfinal, _dummy, _border, hfinalH⟩ := hrecords w _ hrunCpRec
  have hpropW' : run.proper.nodes[w]? = some final := by rw [hnodes]; exact hfinal
  have hgetW : cg.nodes.getD w default = wNode := by
    rw [List.getD_eq_getElem?_getD, hw]; rfl
  have hframeW : frameRect P cg run w = nodeRect cg run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hbottom]
    rfl
  rw [hframeW, nodeRect_of_record hpropW']
  have hzero : final.node.h = 0 := by
    have heq := hfinalH
    have hcond : ((⟨wNode, false, none, false⟩ : ProperNode).node.border == -2 ||
        (⟨wNode, false, none, false⟩ : ProperNode).node.border == 2) = true := by
      simp only [hbottom]
      decide
    have hcz : (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))).node.h = 0 := by
      unfold titleF clearF
      simp only [hcond, ↓reduceIte]
    rw [hcz] at heq
    exact heq
  simp only [hzero]
  omega

/-- Closed exact bottom case: direct height argument, no witness needed. -/
theorem XL_loopRectBottomReal_holds {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult} :
    XL_LoopRectBottomReal exactIds inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect nodeV hnodeV hbV
  have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
  have hflat := xl_bottomFrameHeight (P := execution.params)
    (exact := exactDecls exactIds inp)
    (hrun := hrun) (w := v) (wNode := nodeV) hnodeV hbV
  have hw0 : (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v).h ≤ 0 := hflat
  omega

/-- X exact-source border-zero (copy of the private `X_exclusive_source_border_zero`). -/
private theorem xl_exclusive_source_border_zero {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hlinesLen : execution.lines.length = inp.boxes.length)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hex : source.exclusive = true) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hrole : source.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hex
  have hkeyLen : key < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hkeyLen, rfl⟩
  obtain ⟨node0, hnode0, hborder0⟩ :=
    measuredGraph_exclusive_node_border_zero execution.checked
      execution.graph0_eq hline hsource hrole
  obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode0
  exact ⟨node, hnode, hborder.trans hborder0⟩

/-- X placed-component rect entry (copy of `loopRectCross_rects_get` over exact bounds). -/
private theorem xl_loopRectCross_rects_get (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) {i : Nat}
    (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run 0 labels loops).rects[i]? =
      some (shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  simp only [placeComponentExact, placeBoundsX, List.getElem?_map, List.getElem?_range hi,
    Option.map_some]

/-- X exclusive witness (replay of `loopRect_exclusive_witness` without `IsReal`). -/
private theorem xl_exclusive_witness {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run}
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {key : Nat} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source)
    (hexcl : source.exclusive = true)
    (hmem : key ∈ q.1.1) :
    ∃ w : Nat,
      q.1.1[w]? = some key ∧ source.role = BoxRole.node ∧
      w < (componentCandidate execution.graph q.1.1 candidate).nodes.length ∧
      ((componentCandidate execution.graph q.1.1 candidate).nodes.getD w default).border = 0 ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default))) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run w)))) := by
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
  have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
    have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length = q.1.1.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hv).1
  have hkeylen : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hentry := X_chosen_part_frame_entry hpart hv
  have hval := actual_components_packed_rect_valueX (by rfl) execution.components_eq
    execution.packed_eq packed hpack hselected hentry hkeysize default
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx
  obtain ⟨gnode, _hgnode, hb0⟩ :=
    xl_exclusive_source_border_zero execution hwf hlinesLen hsource hexcl
  have hrole : source.role = BoxRole.node := by
    have hnotgroup : source.role ≠ BoxRole.group :=
      wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hexcl
    cases hr : source.role with
    | node => rfl
    | group => exact absurd hr hnotgroup
  have hcand : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? =
      some gnode := by
    have hmap : (componentCandidate execution.graph q.1.1 candidate).nodes =
        q.1.1.map fun k => execution.graph.nodes.getD k default := by
      rw [componentCandidate_nodes]
      simp only [componentGraph]
    have hget : execution.graph.nodes.getD key default = gnode := by
      have hmemk : execution.graph.nodes[key]? = some gnode := _hgnode
      rw [List.getD_eq_getElem?_getD, hmemk, Option.getD_some]
    rw [hmap]
    simp only [List.getElem?_map, hv, Option.map_some, hget]
  have hborder : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border = 0 := by
    have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default = gnode := by
      rw [List.getD_eq_getElem?_getD, hcand, Option.getD_some]
    rw [hget]
    exact hb0
  refine ⟨v, hv, hrole, hvlen, hborder, ?_⟩
  exact congrArg (fun r => shiftRect execution.params.canvasMargin
    execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH r)) hval

/-- X scene-box origin (copy of `loopRect_box_origin` over `boxes_eq_mapX`). -/
private theorem xl_box_origin {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {b : Box} (hbmem : b ∈ res.scene.boxes) :
    ∃ key source, inp.boxes[key]? = some source ∧ source.exclusive = b.exclusive ∧
      b.rect =
        shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD key default)) := by
  rw [execution.boxes_eq_mapX] at hbmem
  obtain ⟨pair, hpair, hboxeq⟩ := List.mem_map.mp hbmem
  have hsource : inp.boxes[pair.2]? = some pair.1 :=
    List.mem_zipIdx_iff_getElem?.mp hpair
  refine ⟨pair.2, pair.1, hsource, ?_, ?_⟩
  · exact congrArg Box.exclusive hboxeq
  · exact (congrArg Box.rect hboxeq).symm

/-- X foreign part lookup (copy of `loopRect_foreignPart` over `SceneExecutionX`). -/
private theorem xl_foreignPart {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed)
    {keyB : Nat} (hkeyBlen : keyB < inp.boxes.length) :
    ∃ (partB : List Nat × Part) (cB posB : Nat),
      execution.componentsAcc.parts[cB]? = some partB ∧
      partB.1[posB]? = some keyB ∧ cB < packed.boxes.length := by
  obtain ⟨partB, hpartBmem, entry, hentrymem, hentrykey⟩ :=
    sceneExecutionX_parts_entry execution hkeyBlen
  obtain ⟨cB, hcBget⟩ := List.mem_iff_getElem?.mp hpartBmem
  have hposmem : entry.1 ∈ partB.1 := (List.of_mem_zip hentrymem).1
  obtain ⟨posB, hposB⟩ := List.getElem?_of_mem hposmem
  rw [hentrykey] at hposB
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hcBget).1
    omega
  exact ⟨partB, cB, posB, hcBget, hposB, hcBlen⟩

/-- X transported shelf rect (inline copy of `shelfRectT` over `SceneExecutionX`). -/
private def xl_shelfRectT {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State) (c : Nat) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (packed.boxes[c]?.getD default))

/-- X transport of a part-local rect (inline copy of `partRectT` over `SceneExecutionX`). -/
private def xl_partRectT {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State) (c : Nat) (r : Rect) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (shiftRect (packed.boxes[c]?.getD default).x
        (packed.boxes[c]?.getD default).y r))

/-- X shelf disjointness (copy of `partsShelvesDisjoint_of_pack` over `SceneExecutionX`). -/
private theorem xl_partsShelvesDisjoint_of_pack {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionX exactIds inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed) :
    ∀ (c c' : Nat), c < packed.boxes.length → c' < packed.boxes.length → c ≠ c' →
      Disjoint (xl_shelfRectT execution packed c) (xl_shelfRectT execution packed c') := by
  intro c c' hc hc' hne
  have hcD : packed.boxes[c]?.getD default = packed.boxes[c] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩]
  have hcD' : packed.boxes[c']?.getD default = packed.boxes[c'] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc', rfl⟩]
  simp only [xl_shelfRectT]
  rw [hcD, hcD']
  exact orient_transport_disjoint (Pack.pack_boxes_disjoint hpack c c' hc hc' hne)
/-- Residual: distinct border-0 run frames are disjoint over the exact run. -/
def XL_FixedDisjoint (exactIds : List String) : Prop :=
  ∀ (P : Params) (inp : Input) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions)
    (_hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {u v : Nat} {nodeU nodeV : Node},
    cg.nodes[u]? = some nodeU → cg.nodes[v]? = some nodeV →
    nodeU.border = 0 → nodeV.border = 0 → u ≠ v →
    Disjoint (frameRect P cg run u) (frameRect P cg run v)

/-- X rect containment (copy of `part_rects_within_shelf` over exact parts). -/
private theorem xl_part_rects_within_shelf {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q =>
        Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    ∀ r ∈ part.2.rects,
      (xl_shelfRectT execution packed c).Contained
        (xl_partRectT execution packed c r) := by
  have hmemlist : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hmem
  have hbounded := exactPartsBounded' execution part hmemlist
  unfold PartBounded at hbounded
  have hmapLen : c < (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hmem).1
  have hpartget := (List.getElem?_eq_some_iff.mp hmem).2
  have hitem : (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area))[c] =
      Pack.Item.mk part.2.width part.2.height part.2.area := by
    rw [List.getElem_map, hpartget]
  obtain ⟨hsw, hsh⟩ := packShelfDims hpack (by omega : c < packed.boxes.length) hmapLen
  intro r hr
  have hrb := (by obtain ⟨_, _, hrects, _, _, _⟩ := hbounded; exact hrects r hr)
  have hcD : packed.boxes[c]?.getD default = packed.boxes[c] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩]
  simp only [xl_shelfRectT, xl_partRectT, hcD]
  refine orient_transport_contained ?_
  simp only [shiftRect, Rect.Contained]
  obtain ⟨hr1, hr2, hr3, hr4, _, _⟩ := hrb
  have hwb : packed.boxes[c].w = part.2.width := by rw [hsw, hitem]
  have hhb : packed.boxes[c].h = part.2.height := by rw [hsh, hitem]
  rw [hwb, hhb]
  omega

/-- X fixed-owner foreign vehicle (copy of `loopRectFixed_foreign_false`). -/
private theorem xl_Fixed_foreign_false {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box)
    (_hreal : RouteImpl.IsReal run.proper v)
    (_hbmem : b ∈ res.scene.boxes) (_hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))))
    {node : Node}
    (hnode : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node)
    {keyB : Nat} {sourceB : ModelBox}
    (hsourceB : inp.boxes[keyB]? = some sourceB)
    (hbrectB : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default)))
    (hforeign : keyB ∉ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hkeyBlen : keyB < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceB).1
  obtain ⟨partB, cB, posB, hkB, hposB, _hcBlen⟩ :=
    xl_foreignPart execution packed hpack hkeyBlen
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  have hne : c ≠ cB := by
    intro heq
    subst heq
    have hqeq : q.1 = partB := Option.some.inj (hmemc.symm.trans hkB)
    have hmem : keyB ∈ q.1.1 := by
      rw [hqeq]
      exact List.mem_of_getElem? hposB
    exact hforeign hmem
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hclen : c < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
    omega
  have hvlen : v <
      (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hR : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minX)
    (-(placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minY)
    (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v)) ∈ q.1.2.rects := by
    rw [hpart]
    exact List.mem_of_getElem?
      (xl_loopRectCross_rects_get execution.params _ _ _ _ hvlen)
  have hcontR := xl_part_rects_within_shelf execution packed hpack hmemc hclen _ hR
  have hshelfC : packed.boxes[c]? = some q.2 :=
    (List.getElem?_zip_eq_some.mp hselected).2
  have hL : xl_partRectT execution packed c
      (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
    unfold xl_partRectT
    rw [hshelfC, Option.getD_some]
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hkB).1
    omega
  obtain ⟨boxB, hboxB⟩ : ∃ boxB, packed.boxes[cB]? = some boxB :=
    ⟨packed.boxes[cB], List.getElem?_eq_getElem hcBlen⟩
  obtain ⟨candB, runB, loopsB, _areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    part_frame_lookupX execution packed hpack hkB hboxB
  obtain ⟨fB, hfBdef⟩ : ∃ f : Rect, f = shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB) :=
    ⟨_, rfl⟩
  have hval : execution.packedAcc.rects.getD keyB default =
      shiftRect boxB.x boxB.y fB := by
    rw [hfBdef]
    exact hlookupB posB keyB hposB hkeyBlen
  have hiB : posB <
      (componentCandidate execution.graph partB.1 candB).nodes.length := by
    have hlen : (componentCandidate execution.graph partB.1 candB).nodes.length = partB.1.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hposB).1
  have hfBmem : fB ∈ partB.2.rects := by
    rw [hfBdef, hpartdefB]
    exact List.mem_of_getElem?
      (xl_loopRectCross_rects_get execution.params _ _ _ _ hiB)
  have hcontB := xl_part_rects_within_shelf execution packed hpack hkB hcBlen _ hfBmem
  have hdisjAll := xl_partsShelvesDisjoint_of_pack hpack
  have hRHS : (shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect boxB.x boxB.y fB))) = xl_partRectT execution packed cB fB := by
    unfold xl_partRectT
    rw [hboxB, Option.getD_some]
  have hmiss : ¬ (xl_partRectT execution packed c
      (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v))).meetsInterior
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [hval, hRHS]
    intro hmeet
    exact hdisjAll c cB hclen hcBlen hne
      (meetsInterior_of_contained_inner hcontB
        (meetsInterior_of_contained_outer hcontR hmeet))
  have hdisL : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))))
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [← hL]
    exact hmiss
  exact loopRect_crossPart_false hrect hbrectB hdisL hposW hposH
/-- Closed exact fixed case modulo the run-level disjointness residual. -/
theorem XL_loopRectFixedReal_holds {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    (hdisj : XL_FixedDisjoint exactIds) :
    XL_LoopRectFixedReal exactIds inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect nodeV keyV srcV hnodeV hbV hkeyV hsrcV hfixV
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    xl_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · obtain ⟨w, hw, hroleW, hwlen, hbord0, hpackeq⟩ :=
      xl_exclusive_witness execution hwf packed hpack hselected hpart hsourceB hexclB hmem
    have hnodeW : (componentCandidate execution.graph q.1.1 candidate).nodes[w]? =
        some ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen) :=
      List.getElem?_eq_getElem hwlen
    have hbW : ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen).border
        = 0 := by
      have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
          (componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwlen, Option.getD_some]
      rw [← hget]
      exact hbord0
    have hframe : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v := by
      have hww : shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBoundsX execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (-(placeBoundsX execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run w)))) =
          shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect q.2.x q.2.y
                (shiftRect (0 - (placeBoundsX execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minX)
                  (-(placeBoundsX execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minY)
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
        rw [← hpackeq, ← hbrectB]
        exact hrect
      exact loopTransport_cancel hww
    have hposV := loopRect_frame_pos_of_rectEq hrect hposW hposH
    have hpos : 0 < (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w).w ∧
        0 < (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run w).h := by
      rw [hframe]
      exact hposV
    by_cases heq : v = w
    · exact loopRectFixed_samePart_refl hw hsourceB hroleW heq
    · have hne : w ≠ v := fun h => heq h.symm
      have hdis := hdisj execution.params inp
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        (candidateOrder candidate) hrun hnodeW hnodeV hbW hbV hne
      exact False.elim (loopRect_frameNe_of_disjoint hdis hframe hpos.1 hpos.2)
  · exact False.elim (xl_Fixed_foreign_false execution hwf candidate run packed hpack c q
      hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hsourceB hbrectB hmem hposW hposH)
/-- Residual: a plain run frame never equals a group-top run frame over the exact run. -/
def XL_TopSamePart (exactIds : List String) : Prop :=
  ∀ (P : Params) (inp : Input) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions)
    (_hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {v w : Nat} {node member : Node},
    cg.nodes[v]? = some node → node.border = -2 →
    cg.nodes[w]? = some member → member.border = 0 →
    frameRect P cg run w = frameRect P cg run v → False

/-- X top foreign vehicle (copy of `loopRectTop_crossPart`). -/
private theorem xl_Top_foreign_false {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box)
    (_hreal : RouteImpl.IsReal run.proper v)
    (_hbmem : b ∈ res.scene.boxes) (_hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (-(placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))))
    {node : Node}
    (hnode : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node)
    (_hbord : node.border = -2)
    {keyB : Nat} {sourceB : ModelBox}
    (hsourceB : inp.boxes[keyB]? = some sourceB)
    (hbrectB : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default)))
    (hforeign : keyB ∉ q.1.1)
    (hposW : 0 < b.rect.w) (hposH : 0 < b.rect.h) :
    False := by
  have hkeyBlen : keyB < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hsourceB).1
  obtain ⟨partB, cB, posB, hkB, hposB, _hcBlen⟩ :=
    xl_foreignPart execution packed hpack hkeyBlen
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  have hne : c ≠ cB := by
    intro heq
    subst heq
    have hqeq : q.1 = partB := Option.some.inj (hmemc.symm.trans hkB)
    have hmem : keyB ∈ q.1.1 := by
      rw [hqeq]
      exact List.mem_of_getElem? hposB
    exact hforeign hmem
  have hvlen : v <
      (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hplen : packed.boxes.length = execution.componentsAcc.parts.length := by
    rw [Pack.pack_count hpack, List.length_map]
  have hclen : c < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hmemc).1
    omega
  have hR : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minX)
    (-(placeBoundsX execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      loops).minY)
    (frameRect execution.params
      (componentCandidate execution.graph q.1.1 candidate) run v)) ∈ q.1.2.rects := by
    rw [hpart]
    exact List.mem_of_getElem?
      (xl_loopRectCross_rects_get execution.params _ _ _ _ hvlen)
  have hcontR := xl_part_rects_within_shelf execution packed hpack hmemc hclen _ hR
  have hshelfC : packed.boxes[c]? = some q.2 :=
    (List.getElem?_zip_eq_some.mp hselected).2
  have hL : xl_partRectT execution packed c
      (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v)) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
    unfold xl_partRectT
    rw [hshelfC, Option.getD_some]
  have hcBlen : cB < packed.boxes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hkB).1
    omega
  obtain ⟨boxB, hboxB⟩ : ∃ boxB, packed.boxes[cB]? = some boxB :=
    ⟨packed.boxes[cB], List.getElem?_eq_getElem hcBlen⟩
  obtain ⟨candB, runB, loopsB, _areaB, _hrunB, _hloopsB, hpartdefB, hlookupB⟩ :=
    part_frame_lookupX execution packed hpack hkB hboxB
  obtain ⟨fB, hfBdef⟩ : ∃ f : Rect, f = shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph partB.1 candB) runB
        execution.measured loopsB).minY)
      (frameRect execution.params
        (componentCandidate execution.graph partB.1 candB) runB posB) :=
    ⟨_, rfl⟩
  have hval : execution.packedAcc.rects.getD keyB default =
      shiftRect boxB.x boxB.y fB := by
    rw [hfBdef]
    exact hlookupB posB keyB hposB hkeyBlen
  have hiB : posB <
      (componentCandidate execution.graph partB.1 candB).nodes.length := by
    have hlen : (componentCandidate execution.graph partB.1 candB).nodes.length = partB.1.length := by
      rw [componentCandidate_nodes]
      simp only [componentGraph, List.length_map]
    rw [hlen]
    exact (List.getElem?_eq_some_iff.mp hposB).1
  have hfBmem : fB ∈ partB.2.rects := by
    rw [hfBdef, hpartdefB]
    exact List.mem_of_getElem?
      (xl_loopRectCross_rects_get execution.params _ _ _ _ hiB)
  have hcontB := xl_part_rects_within_shelf execution packed hpack hkB hcBlen _ hfBmem
  have hdisjAll := xl_partsShelvesDisjoint_of_pack hpack
  have hRHS : (shiftRect execution.params.canvasMargin
      execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect boxB.x boxB.y fB))) = xl_partRectT execution packed cB fB := by
    unfold xl_partRectT
    rw [hboxB, Option.getD_some]
  have hmiss : ¬ (xl_partRectT execution packed c
      (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v))).meetsInterior
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [hval, hRHS]
    intro hmeet
    exact hdisjAll c cB hclen hcBlen hne
      (meetsInterior_of_contained_inner hcontB
        (meetsInterior_of_contained_outer hcontR hmeet))
  have hdisL : Disjoint
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))))
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD keyB default))) := by
    rw [← hL]
    exact hmiss
  exact loopRect_crossPart_false hrect hbrectB hdisL hposW hposH

/-- Closed exact top case modulo the run-level same-part residual. -/
theorem XL_loopRectTopReal_holds {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    (hsame : XL_TopSamePart exactIds) :
    XL_LoopRectTopReal exactIds inp o res := by
  intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
    v b hreal hbmem hexcl hposW hposH hrect node hnodeV hbV
  obtain ⟨keyB, sourceB, hsourceB, hboxexcl, hbrectB⟩ :=
    xl_box_origin execution hbmem
  have hexclB : sourceB.exclusive = true := by rw [hboxexcl]; exact hexcl
  by_cases hmem : keyB ∈ q.1.1
  · obtain ⟨w, hw, _hroleW, hwlen, hbord0, hpackeq⟩ :=
      xl_exclusive_witness execution hwf packed hpack hselected hpart hsourceB hexclB hmem
    have hnodeW : (componentCandidate execution.graph q.1.1 candidate).nodes[w]? =
        some ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen) :=
      List.getElem?_eq_getElem hwlen
    have hbW : ((componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen).border
        = 0 := by
      have hget : (componentCandidate execution.graph q.1.1 candidate).nodes.getD w default =
          (componentCandidate execution.graph q.1.1 candidate).nodes[w]'hwlen := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwlen, Option.getD_some]
      rw [← hget]
      exact hbord0
    have hframe : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run w =
        frameRect execution.params
          (componentCandidate execution.graph q.1.1 candidate) run v := by
      have hww : shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y
              (shiftRect (0 - (placeBoundsX execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minX)
                (-(placeBoundsX execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                  loops).minY)
                (frameRect execution.params
                  (componentCandidate execution.graph q.1.1 candidate) run w)))) =
          shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (shiftRect q.2.x q.2.y
                (shiftRect (0 - (placeBoundsX execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minX)
                  (-(placeBoundsX execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minY)
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
        rw [← hpackeq, ← hbrectB]
        exact hrect
      exact loopTransport_cancel hww
    exact False.elim (hsame execution.params inp
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      (candidateOrder candidate) hrun hnodeV hbV hnodeW hbW hframe)
  · exact False.elim (xl_Top_foreign_false execution hwf candidate run packed hpack c q
      hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnodeV hbV
      hsourceB hbrectB hmem hposW hposH)
end PipelineImpl
end Layered
end Elegant

