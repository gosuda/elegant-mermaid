import Elegant.Layered.SizingFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Order
import Elegant.Layered.CgShape
import Elegant.Layered.SizingCoverageBridge

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The horizontal span of a group frame is exactly the span of its border
rectangles; no `clusterPad` is added.  When the border list is empty, the
width is `0`. This is a frameRect identity only, not a reachable execution
counterexample: the empty case is not shown to occur for an executed group. -/
theorem frameRect_group_width_eq_horizontal_span
    {P : Params} {cg : Graph} {run : Run} {i : Nat} {node : Node}
    (hnode : cg.nodes[i]? = some node) (hborder : node.border = -2) :
    (frameRect P cg run i).w =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).right -
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minX := by
  simp [frameRect, List.getD_eq_getElem?_getD, hnode, hborder]

/-- Decidable identity: a group node whose border filter is empty has frame
width `0`. This is a filter identity on an arbitrary run, not an executable
witness; reachability of the empty filter is not established here. -/
theorem frameRect_group_empty_borders_counterexample
    {P : Params} {cg : Graph} {run : Run} {i : Nat} {node : Node}
    (hnode : cg.nodes[i]? = some node) (hborder : node.border = -2)
    (hempty : (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) = [])
    (hpad : 0 < P.clusterPad) :
    (frameRect P cg run i).w < 2 * P.clusterPad := by
  rw [frameRect_group_width_eq_horizontal_span hnode hborder, hempty]
  simp [boundsOf]
  omega

/-- The vertical span of a group frame is exactly the span of the rectangles
of every proper node whose cluster path contains the group declaration. -/
theorem frameRect_group_height_eq_vertical_span
    {P : Params} {cg : Graph} {run : Run} {i : Nat} {node : Node}
    (hnode : cg.nodes[i]? = some node) (hborder : node.border = -2) :
    (frameRect P cg run i).h =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom -
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minY := by
  simp [frameRect, List.getD_eq_getElem?_getD, hnode, hborder]

/-- The fold accumulator of `boundsOf` keeps its `bottom` above every member's
`y + h`. -/
theorem foldl_bounds_bottom {rects : List Rect} (b : Bounds) :
    b.bottom ≤ (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).bottom ∧
    ∀ r ∈ rects, r.y + r.h ≤ (rects.foldl (fun b r => ⟨min b.minX r.x,
        min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).bottom := by
  induction rects generalizing b with
  | nil => exact ⟨Int.le_refl _, by simp⟩
  | cons a rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih ⟨min b.minX a.x, min b.minY a.y,
      max b.right (a.x + a.w), max b.bottom (a.y + a.h)⟩
    refine ⟨?_, ?_⟩
    · exact Int.le_trans (Int.le_max_left _ _) h1
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · exact Int.le_trans (Int.le_max_right _ _) h1
      · exact h2 r hrest

/-- The fold accumulator of `boundsOf` keeps its `minY` below every member's
`y`. -/
theorem foldl_bounds_minY {rects : List Rect} (b : Bounds) :
    (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).minY ≤ b.minY ∧
    ∀ r ∈ rects, (rects.foldl (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) b).minY ≤ r.y := by
  induction rects generalizing b with
  | nil => exact ⟨Int.le_refl _, by simp⟩
  | cons a rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih ⟨min b.minX a.x, min b.minY a.y,
      max b.right (a.x + a.w), max b.bottom (a.y + a.h)⟩
    refine ⟨?_, ?_⟩
    · exact Int.le_trans h1 (Int.min_le_left _ _)
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hrest
      · exact Int.le_trans h1 (Int.min_le_right _ _)
      · exact h2 r hrest

/-- The height of `boundsOf rects []` is at least the height of every member
rectangle. -/
theorem boundsOf_height_ge_member {rects : List Rect} {r : Rect}
    (hm : r ∈ rects) :
    r.h ≤ (boundsOf rects []).bottom - (boundsOf rects []).minY := by
  cases rects with
  | nil => cases hm
  | cons a rest =>
    have hb := foldl_bounds_bottom (rects := a :: rest) ⟨a.x, a.y, 0, 0⟩
    have hmY := foldl_bounds_minY (rects := a :: rest) ⟨a.x, a.y, 0, 0⟩
    have hry := hb.2 r hm
    have hminy := hmY.2 r hm
    change r.h ≤ ((a :: rest).foldl (fun (b : Bounds) (r : Rect) =>
        ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
        ⟨a.x, a.y, 0, 0⟩).bottom -
      ((a :: rest).foldl (fun (b : Bounds) (r : Rect) =>
        ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
        ⟨a.x, a.y, 0, 0⟩).minY
    omega

/-- The border-`3` title reservation produced by `coordinateGraph` for a
non-dummy border-`-2` node `nd` at index `i` of `p`: it sits at index
`p.nodes.length + j` where `j` is the `titleNodes` index of `(nd, i)`, keeps
`nd`'s height and cluster path, and has border `3`. -/
theorem coordinateGraph_title_copy {P : Params} {p : Proper} {i : Nat} {nd : ProperNode}
    (hi : p.nodes[i]? = some nd) (hb : nd.node.border = -2) (hd : nd.dummy = false) :
    ∃ (j : Nat) (res : ProperNode), (coordinateGraph P p).nodes[p.nodes.length + j]? = some res ∧
      res.node.border = 3 ∧ res.node.h = nd.node.h ∧
      res.node.clusterPath = nd.node.clusterPath ∧ res.dummy = false := by
  classical
  have hsized : (sizeProperPorts P p).nodes[i]? = some nd := by
    have hnodes : (sizeProperPorts P p).nodes = p.nodes.zipIdx.map fun q =>
      if q.1.dummy || q.1.node.border != 0 then q.1
      else
        let incoming := ((p.edges.filter fun edge => edge.head == q.2).map (·.tail)).eraseDups.length
        let outgoing := ((p.edges.filter fun edge => edge.tail == q.2).map (·.head)).eraseDups.length
        { q.1 with node := { q.1.node with
          w := max q.1.node.w ((((max incoming outgoing : Nat) + 1 : Nat) : Int) * P.portGap) } } := rfl
    rw [hnodes]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some]
    simp [hb]
  have hmem : (nd, i) ∈ titleNodes (sizeProperPorts P p) := by
    unfold titleNodes
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr hsized
    · simp [hb]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hjlt : j < (titleNodes (sizeProperPorts P p)).length :=
    (List.getElem?_eq_some_iff.mp hj).1
  have hv_lt : p.nodes.length + j <
      (titleReservations (sizeProperPorts P p)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map, sizeProperPorts_length]
    omega
  have htr : (titleReservations (sizeProperPorts P p)).nodes[p.nodes.length + j]? =
      some (copyF (nd, i)) := by
    rw [titleReservations_nodes]
    rw [List.getElem?_append_right (by
      simp only [List.length_map, sizeProperPorts_length]
      omega : ((sizeProperPorts P p).nodes.map titleF).length ≤ p.nodes.length + j)]
    have hsub : p.nodes.length + j - ((sizeProperPorts P p).nodes.map titleF).length = j := by
      simp only [List.length_map, sizeProperPorts_length]
      omega
    rw [hsub, List.getElem?_map, hj]
    rfl
  obtain ⟨extra, hcb_nodes, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hcb : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[p.nodes.length + j]? =
      some (copyF (nd, i)) := by
    rw [hcb_nodes, List.getElem?_append_left hv_lt]
    exact htr
  have hcf : clearF (copyF (nd, i)) = copyF (nd, i) := by
    simp [clearF, copyF]
  have hce : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[p.nodes.length + j]? =
      some (copyF (nd, i)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hcb]
    simp only [Option.map_some, Option.some.injEq]
    exact hcf
  obtain ⟨out, hout, -⟩ := materialize_exists _ hce
  obtain ⟨m, hm, -, -, -, hmeq⟩ := materialize_lookup _ hout
  have hmres : m = copyF (nd, i) := Option.some.inj (hm.symm.trans hce)
  subst m
  have hout_eq : out = copyF (nd, i) := hmeq hd
  subst out
  exact ⟨j, copyF (nd, i), hout, rfl, rfl, rfl, hd⟩

/-- A successful `componentRun` on a border-`-2` node `node` at index `i`
produces a border-`3` reservation node in `run.proper` at index
`labeled.nodes.length + j` that preserves `node`'s height and cluster path.
This is the executed provenance of the group title reservation: the node is
the `copyF` image of the normalized/already-labelled node, carried unchanged
through `clearProxyExtents`, `proxyWidths` (border `3` is neither `-2` nor
`2`), and `dropSynthetic`. -/
theorem componentRun_group_reservation {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node) (hb : node.border = -2) :
    ∃ (v : Nat) (res : ProperNode), run.proper.nodes[v]? = some res ∧
      res.node.border = 3 ∧ res.node.h = node.h ∧
      res.node.clusterPath = node.clusterPath := by
  obtain ⟨ranks, p0, labeled, q0, hnorm, hlabels, hcoord, -, -, hproxy, hdrop,
    -, -, -, -, -⟩ := componentRun_spec h
  have hp0 : p0.nodes[i]? = some ⟨node, false, none, false⟩ :=
    normalize_node_record hnorm hn
  have hlab : labeled.nodes[i]? = some ⟨node, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels hp0 (by rfl)
  obtain ⟨j, res, hcoord', hb3, hres_h, hres_path, -⟩ :=
    coordinateGraph_title_copy hlab hb (by rfl)
  have hv : run.coordinateProper.nodes[labeled.nodes.length + j]? = some res := by
    rw [← hcoord]
    exact hcoord'
  obtain ⟨-, -, -, -, -, hrel2⟩ := proxyWidths_rel hproxy
  have hbnd : ¬ (res.node.border = -2 ∨ res.node.border = 2) := by
    rw [hb3]
    decide
  have hq0 : q0.nodes[labeled.nodes.length + j]? = some res :=
    (hrel2 _ res hv hbnd).1
  have hnodes : run.proper.nodes = q0.nodes := by
    have h := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at h
    exact h.symm
  have hproper : run.proper.nodes[labeled.nodes.length + j]? = some res := by
    rw [hnodes]
    exact hq0
  exact ⟨labeled.nodes.length + j, res, hproper, hb3, hres_h, hres_path⟩

/-- Actual height bound for a nonfixed group frame inside a successful
`componentRun`: if `node.clusterPath` contains its own declaration (the shape
produced by `Compound.prepare` for group boxes) and `th` is at most the node's
stored height minus `clusterPad`, then `th + clusterPad` is at most the frame
height.  The proof transports the executed reservation node's height through
`frameRect`'s vertical `boundsOf`: the reservation's `rectAt` is a member of
the vertical rectangle list, so the frame height is at least the reservation
height, which equals the group node's stored height. -/
theorem componentRun_group_frame_height_ge
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node) (hb : node.border = -2)
    (hmem : node.clusterPath.contains node.decl)
    {th : Int} (hth : th + P.clusterPad ≤ node.h) :
    th + P.clusterPad ≤ (frameRect P cg run i).h := by
  obtain ⟨v, res, hv, -, hres_h, hres_path⟩ :=
    componentRun_group_reservation h hn hb
  have hrect : Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains node.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
    refine List.mem_filterMap.mpr ⟨(res, v), ?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr hv
    · change (if res.node.clusterPath.contains node.decl then
          some (Labels.rectAt run.proper run.xs run.ys v) else none) = _
      rw [hres_path, ite_eq_left hmem]
  have hge := boundsOf_height_ge_member hrect
  have hrect_h : (Labels.rectAt run.proper run.xs run.ys v).h = node.h := by
    show RouteImpl.nodeH run.proper v = node.h
    unfold RouteImpl.nodeH
    rw [hv]
    exact hres_h
  rw [frameRect_group_height_eq_vertical_span hn hb]
  omega

theorem actual_group_self_membership
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g : Graph}
    (hg : measuredGraph P inp o lines = .ok g)
    {comp : List Nat} {index i : Nat} {top : Node} {box : ModelBox}
    (htop : (componentCandidate g comp index).nodes[i]? = some top)
    (hborder : top.border = -2)
    (hbox : inp.boxes[comp.getD i 0]? = some box) :
    top.clusterPath.contains top.decl := by
  obtain ⟨j, _, hkey, hget, hdecl, _, hrole, hfixed, _, _⟩ :=
    actual_title_metadata hg htop hborder hbox
  rw [hkey] at hbox
  unfold measuredGraph at hg
  obtain ⟨initial, _, hg⟩ := bind_ok hg
  obtain ⟨edges, _, hg⟩ := bind_ok hg
  obtain ⟨metric, _, hg⟩ := bind_ok hg
  obtain ⟨labels, _, hg⟩ := bind_ok hg
  obtain ⟨nodes, _, hg⟩ := bind_ok hg
  have heq := Except.ok.inj hg
  subst g
  have hj : j < nodes.length := by
    by_cases hj : j < nodes.length
    · exact hj
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ j
        (by dsimp only; omega) hget
      omega
  have hpreparedBox :
      (inp.boxes.map (fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b))[j]? = some box := by
    simp [List.getElem?_map, hbox, hfixed]
  have hpath := Compound.prepare_group_clusterPath _ _ _ _ hj
    hpreparedBox hrole hget
  rw [hpath, hdecl]
  simp

theorem SceneExecution.component_group_caption_rank_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2)
    {box : ModelBox} (hbox : inp.boxes[key]? = some box)
    {rect : Rect} (hrect : part.2.rects[i]? = some rect) :
    (match o.direction with
      | .LR | .RL =>
        (execution.lines.getD key []).foldl (fun width line => max width line.width) 0
      | .TB | .BT =>
        (max 1 (execution.lines.getD key []).length : Int) * execution.params.lineH) +
      execution.params.clusterPad ≤ rect.h := by
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  have hlocal : (componentCandidate execution.graph part.1 index).nodes[i]? =
      some node := by
    rw [componentCandidate_nodes]
    change (part.1.map (fun key => execution.graph.nodes.getD key default))[i]? =
      some node
    simp only [List.getElem?_map, hkey, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hkeyD : part.1.getD i 0 = key := by
    simp [List.getD, hkey]
  have hboxD : inp.boxes[part.1.getD i 0]? = some box := by
    rw [hkeyD]
    exact hbox
  have hmem := actual_group_self_membership execution.graph_eq hlocal hborder hboxD
  have hcaption := (actual_title_caption_fit execution.graph_eq hlocal hborder).2
  rw [hkeyD] at hcaption
  have hminimum := componentRun_group_frame_height_ge hrun hlocal hborder hmem hcaption
  have hdims :
      part.2.rects.map (fun r => (r.w, r.h)) =
        (List.range (componentCandidate execution.graph part.1 index).nodes.length).map
          (fun j =>
            ((frameRect execution.params
              (componentCandidate execution.graph part.1 index) run j).w,
             (frameRect execution.params
              (componentCandidate execution.graph part.1 index) run j).h)) := by
    rw [hplace]
    exact Layered.placeComponent_rect_dimensions execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
  have hi : i < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hlocal).1
  have hindex := congrArg (fun values : List (Int × Int) => values[i]?) hdims
  simp only [List.getElem?_map, hrect, Option.map_some,
    List.getElem?_range hi] at hindex
  have heq := (Prod.mk.inj (Option.some.inj hindex)).2
  rw [heq]
  exact hminimum

theorem SceneExecution.component_group_caption_oriented_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2)
    {box : ModelBox} (hbox : inp.boxes[key]? = some box)
    {rect : Rect} (hrect : part.2.rects[i]? = some rect) :
    match o.direction with
    | .LR | .RL =>
      (execution.lines.getD key []).foldl (fun width line => max width line.width) 0 +
          execution.params.clusterPad ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).w
    | .TB | .BT =>
      (max 1 (execution.lines.getD key []).length : Int) * execution.params.lineH +
          execution.params.clusterPad ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).h := by
  have hfit := execution.component_group_caption_rank_fit
    hpart hkey hnode hborder hbox hrect
  cases hd : o.direction <;> simp only [hd, orientRect] at hfit ⊢ <;> exact hfit

theorem SceneExecution.group_caption_packed_rank_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {key : Nat} {node : Node}
    (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2)
    {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    ∃ rect, execution.packedAcc.rects[key]? = some rect ∧
      (match o.direction with
        | .LR | .RL =>
          (execution.lines.getD key []).foldl (fun w line => max w line.width) 0
        | .TB | .BT =>
          (max 1 (execution.lines.getD key []).length : Int) * execution.params.lineH) +
        execution.params.clusterPad ≤ rect.h := by
  let caption : Int :=
    (match o.direction with
      | .LR | .RL =>
        (execution.lines.getD key []).foldl (fun w line => max w line.width) 0
      | .TB | .BT =>
        (max 1 (execution.lines.getD key []).length : Int) * execution.params.lineH) +
      execution.params.clusterPad
  let minimum : Nat → Size := fun i => ⟨0, if i = key then caption else 0⟩
  have hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
      (minimum entry.1).w ≤ entry.2.w ∧
        (minimum entry.1).h ≤ entry.2.h := by
    intro part hpart entry hentry
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hentry
    simp only [List.length_zip] at hi
    have hil : i < part.1.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hir : i < part.2.rects.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hpair : (part.1[i], part.2.rects[i]) = entry := by
      simpa only [List.getElem_zip] using heq
    have hkey : part.1[i]? = some entry.1 := by
      rw [List.getElem?_eq_getElem hil, ← hpair]
    have hrect : part.2.rects[i]? = some entry.2 := by
      rw [List.getElem?_eq_getElem hir, ← hpair]
    have hb := execution.components_parts_bounded part hpart
    have hn := hb.2.2.1 entry.2 (List.of_mem_zip hentry).2
    refine ⟨hn.2.2.2.2.1, ?_⟩
    by_cases he : entry.1 = key
    · have hfit := execution.component_group_caption_rank_fit
        (hpart := hpart) (hkey := he ▸ hkey) hnode hborder hsource hrect
      simpa only [minimum, he, ↓reduceIte, caption] using hfit
    · simpa only [minimum, he, ↓reduceIte] using hn.2.2.2.2.2
  obtain ⟨rect, hrect⟩ := execution.packed_rect_exists
    (List.getElem?_eq_some_iff.mp hsource).1
  have hfit := packAcc_rect_minimum_dimensions_of_coverage minimum execution.packed_eq
    (fun i r hr => Or.inr (execution.parts_coverage i r hr)) hparts key rect hrect
  exact ⟨rect, hrect, by simpa only [minimum, ↓reduceIte, caption] using hfit.2⟩

theorem SceneExecution.group_caption_output_rank_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {index : Nat} {box : Box} (hbox : res.scene.boxes[index]? = some box)
    {source : ModelBox} (hsource : inp.boxes[index]? = some source)
    {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hborder : node.border = -2) :
    match o.direction with
    | .LR | .RL =>
      (execution.lines.getD index []).foldl (fun w line => max w line.width) 0 +
        execution.params.clusterPad ≤ box.rect.w
    | .TB | .BT =>
      (max 1 (execution.lines.getD index []).length : Int) * execution.params.lineH +
        execution.params.clusterPad ≤ box.rect.h := by
  obtain ⟨rect, hrect, hfit⟩ :=
    execution.group_caption_packed_rank_fit hnode hborder hsource
  obtain ⟨actual, hactual, hboxeq⟩ := execution.box_index_origin hbox
  rw [hsource] at hactual
  cases Option.some.inj hactual
  have hget : execution.packedAcc.rects.getD index default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hi] using heq
  rw [hboxeq, hget]
  cases hd : o.direction <;>
    simp only [hd, orientRect, shiftRect] at hfit ⊢ <;> exact hfit

end Elegant.Layered.PipelineImpl
