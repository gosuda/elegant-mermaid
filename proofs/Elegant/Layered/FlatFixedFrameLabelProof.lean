import Elegant.Layered.ExpandChildFitPerCallProof
import Elegant.Layered.CaptionFallbackContainProof
import Elegant.Layered.FrameLabelsProof
import Elegant.Layered.RouteLabelLeftoverPairProof
import Elegant.Layered.SeamClosureGlue
import Elegant.Layered.CaptionRunClearClosed
import Elegant.Layered.ForeignBorderDivergeFramedProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem ownerOverlap_of_caption_inside {frame owner label : Rect}
    (howner : owner.Contained label) (hinside : frame.StrictInside label)
    (hw : 0 < owner.w) (hh : 0 < owner.h)
    (hlw : 0 ≤ label.w) (hlh : 0 ≤ label.h) : frame.meetsInterior owner := by
  simp only [Rect.Contained, Rect.StrictInside, Rect.meetsInterior] at *
  constructor <;> omega

private theorem strictInside_of_shiftRect {frame label : Rect} {dx dy : Int}
    (h : (shiftRect dx dy frame).StrictInside (shiftRect dx dy label)) :
    frame.StrictInside label := by
  simp only [Rect.StrictInside, shiftRect] at h ⊢
  omega

private theorem strictInside_of_sceneTransport (direction : Direction)
    {frame label : Rect} {height margin : Int}
    (h : (shiftRect margin margin (orientRect direction height frame)).StrictInside
      (shiftRect margin margin (orientRect direction height label))) :
    frame.StrictInside label := by
  have hinside := strictInside_of_shiftRect h
  cases direction <;> simp only [Rect.StrictInside, orientRect] at hinside ⊢ <;> omega

private theorem axisSeparated_shiftRect {a b : Rect} {dx dy : Int}
    (h : RectAxisSeparated a b) :
    RectAxisSeparated (shiftRect dx dy a) (shiftRect dx dy b) := by
  simp only [RectAxisSeparated, shiftRect] at h ⊢
  omega

private theorem axisSeparated_orientRect (direction : Direction) {a b : Rect} {height : Int}
    (h : RectAxisSeparated a b) :
    RectAxisSeparated (orientRect direction height a) (orientRect direction height b) := by
  cases direction <;> simp only [RectAxisSeparated, orientRect] at h ⊢ <;> omega

private theorem not_strictInside_of_separated {frame other label : Rect}
    (hsep : RectAxisSeparated frame other) (hcontain : other.Contained label)
    (hw : 0 ≤ label.w) (hh : 0 ≤ label.h) : ¬ frame.StrictInside label := by
  intro hinside
  simp only [RectAxisSeparated, Rect.Contained, Rect.StrictInside] at hsep hcontain hinside
  omega

/-- In the measured-but-unplaced branch the default rectangle is on the outer
edge of the packed coordinate system, even after orientation. -/
theorem SceneExecution.defaultLabel_not_strictInside
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {frame : Box} (hframe : frame ∈ res.scene.boxes) :
    ¬ frame.rect.StrictInside
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH default)) := by
  intro hinside
  obtain ⟨key, hk⟩ := List.mem_iff_getElem?.mp hframe
  obtain ⟨_, _, heq⟩ := execution.box_index_origin hk
  obtain ⟨_, _, _, _, _, hnonneg⟩ := packedTransportBounded_of_residuals execution
    (packedLabelsTransport_of_bridge execution)
  have hx := hnonneg key (execution.packedAcc.rects.getD key default) rfl
  rw [heq] at hinside
  have h := strictInside_of_sceneTransport o.direction hinside
  change (execution.packedAcc.rects.getD key default).StrictInside ⟨0, 0, 0, 0⟩ at h
  simp only [Rect.StrictInside] at h
  omega

/-- Route labels in the fixed group's own component cannot lie strictly
inside its plain node frame, including labels with a degenerate rectangle. -/
theorem SceneExecution.routeStack_not_strictInside_fixedFrame
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} {candidate : Nat} {run : Run}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured (candidateOrder candidate) = .ok run)
    {v : Nat} (hv : v < comp.length) {source : ModelBox}
    (hsource : inp.boxes[comp[v]]? = some source) {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry)
    {edge : Nat} {e : Edge} {env label : Rect}
    (hedge : (componentCandidate execution.graph comp candidate).edges[edge]? = some e)
    (henv : labelEnvelope execution.params (componentCandidate execution.graph comp candidate)
      run execution.measured edge e = some env)
    (hlabel : label ∈ Labels.stackRects env.x env.y
      (componentCandidate execution.graph comp candidate).slot
      ((routeLabels execution.measured e.decl).map fun l => (l.width, l.height))) :
    ¬ (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).StrictInside
      label := by
  obtain ⟨node, hnode, hzero⟩ := execution.fixed_candidate_node_border_zero
    comp candidate v hv hsource hfixed
  obtain ⟨actual, _, hactual, hreal, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnode hzero
  have hin := (List.getElem?_eq_some_iff.mp hactual).1
  have hreal' : RouteImpl.IsReal run.proper v := by
    intro nd hnd
    rw [hactual] at hnd
    exact (Option.some.inj hnd) ▸ hreal
  let cg := componentCandidate execution.graph comp candidate
  have hget : (cg.nodes.getD v default).border = 0 := by
    simp [cg, List.getD_eq_getElem?_getD, hnode, hzero]
  have hrect := plain_frame_eq_boxRect execution.params cg run v hin
    (by rw [hget]; decide)
  intro hinside
  change (frameRect execution.params cg run v).StrictInside label at hinside
  by_cases hloop : e.tail = e.head
  · have hres := loopReservation_executed execution comp candidate run e.tail hcomp hrun
    change LoopReservation cg run execution.measured e.tail at hres
    let sizes := loopSizes cg.edges execution.measured e.tail cg.slot
    have hmemEdge : e ∈ loopEdges cg.edges e.tail :=
      List.mem_filter.mpr ⟨List.mem_of_getElem? hedge, by simp [hloop]⟩
    have hsized : stackSize cg.slot (routeLabels execution.measured e.decl) ∈ sizes :=
      List.mem_map.mpr ⟨e, hmemEdge, rfl⟩
    have hwidths : ∀ s ∈ sizes, 0 ≤ s.width := by
      intro s hm
      obtain ⟨owner, _, rfl⟩ := List.mem_map.mp hm
      rw [stackSize_width_eq]
      exact Labels.stackWidth_nonneg _
    have hcount : 1 ≤ sizes.length :=
      Nat.succ_le_of_lt (List.length_pos_iff.mpr (by
        intro hempty
        rw [hempty] at hsized
        simp at hsized))
    have hslot : 0 ≤ cg.slot := Int.le_of_lt hres.1
    have hband := foldl_max_height_ge sizes (2 * cg.slot)
    change 2 * cg.slot ≤ Loops.band cg.slot sizes at hband
    have hposh : 0 < (sizes.length : Int) * Loops.band cg.slot sizes :=
      Int.mul_pos (by omega) (by have := hres.1; omega)
    have hposw : 0 < cg.slot * ((sizes.length : Int) + 1) :=
      Int.mul_pos hres.1 (by omega)
    have hext := extent_ge_lane_width hslot hwidths hsized hcount
    have hw := hwidths _ hsized
    have hfit := hres.2
    change (sizes.length : Int) * Loops.band cg.slot sizes ≤
      (frameRect default cg run e.tail).h at hfit
    have hexact := run_exact_nil hrun
    have hnotexact : run.exact.contains e.tail = false := by simp [hexact]
    have hfoot : 0 < (loopFootprint cg run execution.measured e.tail).w ∧
        0 < (loopFootprint cg run execution.measured e.tail).h := by
      simp only [loopFootprint, hnotexact, Bool.false_eq_true, ↓reduceIte]
      change 0 < Loops.extent cg.slot sizes ∧ 0 < (frameRect default cg run e.tail).h
      exact ⟨by omega, by omega⟩
    have henvFit := loop_envelope_contained hslot execution.measured_nonneg hexact
      hedge hloop (loop_envelope_eq hloop hexact henv) hfit
    have hsizes : ∀ s ∈ (routeLabels execution.measured e.decl).map
        (fun l => (l.width, l.height)), 0 ≤ s.1 ∧ 0 ≤ s.2 := by
      intro s hm
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
      have hn := execution.measured_nonneg l (List.mem_filter.mp hl).1
      exact ⟨hn.1, hn.2.1⟩
    obtain ⟨hew, heh⟩ := labelEnvelope_loop_size hloop henv
    have hwFit : Labels.stackWidth ((routeLabels execution.measured e.decl).map
        fun l => (l.width, l.height)) ≤ env.w := by
      rw [hew, stackSize_width_eq] <;> exact Int.le_refl _
    have hhFit : Labels.stackHeight cg.slot ((routeLabels execution.measured e.decl).map
        fun l => (l.width, l.height)) ≤ env.h := by
      rw [heh, stackSize_height_eq] <;> exact Int.le_refl _
    obtain ⟨hlw, hlh, hstack⟩ :=
      Labels.stackRects_contained env cg.slot hslot hsizes hwFit hhFit label hlabel
    have hbeyond := beyondProper_closed foreignBorderDivergeStable_framed inp o res hwf hframed
    have htop := loopFootprintTopSeparation_closed inp o res hwf hframed
      (foreignBorderChainXAligned' foreignBorderDivergeStable_framed) hbeyond
    have hdisjoint := loopFootprintSeparation_executed' execution comp candidate run
      e.tail v hcomp hget hrun htop hbeyond
    exact hdisjoint ((Rect.meetsInterior_comm _ _).mp
      (ownerOverlap_of_caption_inside (henvFit.trans hstack) hinside hfoot.1 hfoot.2 hlw hlh))
  · rw [hrect] at hinside
    obtain ⟨hx, size, hsize, hw, hh⟩ := stackRects_entry hlabel
    obtain ⟨measured, hmeasured, rfl⟩ := List.mem_map.mp hsize
    have hdim := execution.measured_nonneg measured (List.mem_filter.mp hmeasured).1
    have hlw : 0 ≤ label.w := hw.symm ▸ hdim.1
    cases hrev : e.reversed
    · have hsep := forwardRealClearScopeFree execution comp candidate run
        (candidateOrder candidate) cg edge e env v label hcomp rfl hrun hedge
        hloop hrev henv hin hreal' hlabel
      have hlh : 0 ≤ label.h := hh.symm ▸ hdim.2.1
      simp only [RectAxisSeparated, Rect.StrictInside] at hsep hinside
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _, _, _⟩ :=
        componentRun_spec hrun
      obtain ⟨_, lane, _, hlane, heq⟩ := reversed_envelope_eq hloop hrev henv
      have hmem := List.mem_of_find?_eq_some hlane
      obtain ⟨_, _, hslot, hlist⟩ := RouteImpl.routeWithLanes_spec hlanes
      rw [hlist] at hmem
      have hright := RouteImpl.plannedLane_right_strict (by omega : 0 ≤ execution.params.slot) hmem
      have hbound := RouteImpl.laneRight_bound run.proper run.xs hin
      have henvx : env.x = lane.lane + cg.slot := by rw [heq]; rfl
      simp only [Rect.StrictInside, boxRect_left, boxRect_w, fdiv2_ediv] at hinside
      rw [fdiv2_ediv] at hbound
      have hext : 0 ≤ ((run.proper.nodes.getD v default).node.loopExtent : Int) := by omega
      have hcgSlot : 0 ≤ cg.slot := componentRun_slot_nonneg (cg := cg) hrun
      show False
      omega

private def shelfBefore (a b : Rect) : Prop :=
  a.y + a.h ≤ b.y ∨ a.x + a.w ≤ b.x

private theorem append_shelfBefore {target gap : Int} {s next : Pack.State} {item : Pack.Item}
    (hg : 0 ≤ gap) (hs : Pack.Inv s) (hp : s.boxes.Pairwise shelfBefore)
    (h : Pack.append target gap s item = .ok next) : next.boxes.Pairwise shelfBefore := by
  unfold Pack.append at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp at h
  all_goals try contradiction
  all_goals subst next
  all_goals obtain ⟨_, _, _, _, _, hempty, _, hb⟩ := hs
  all_goals have hx : s.occupied ≠ true → s.x = 0 :=
    fun hn => hempty (Bool.eq_false_iff.mpr hn)
  all_goals simp only [List.pairwise_append, List.pairwise_singleton, true_and, hp,
    List.mem_singleton, forall_eq]
  all_goals intro old hold
  all_goals obtain ⟨_, _, _, _, _, _, hbottom, hrow⟩ := hb old hold
  all_goals try have hx0 : s.x = 0 := hx (by assumption)
  all_goals simp only [shelfBefore]
  all_goals omega

private theorem fold_shelfBefore {target gap : Int} (hg : 0 ≤ gap) (items : List Pack.Item)
    {s out : Pack.State} (hs : Pack.Inv s) (hp : s.boxes.Pairwise shelfBefore)
    (h : items.foldlM (Pack.append target gap) s = .ok out) :
    out.boxes.Pairwise shelfBefore := by
  induction items generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst out
    exact hp
  | cons item items ih =>
    simp only [List.foldlM_cons] at h
    cases ha : Pack.append target gap s item with
    | error e => simp [ha, bind, Except.bind] at h
    | ok next =>
      simp only [ha, bind, Except.bind] at h
      exact ih (Pack.append_inv hg hs ha) (append_shelfBefore hg hs hp ha) h

private theorem pack_shelfBefore {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    out.boxes.Pairwise shelfBefore := by
  unfold Pack.pack at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i hn
    cases ht : Pack.packingTarget maxWidth gap aspectNum aspectDen items with
    | error e => simp [ht] at h
    | ok target =>
      simp only [ht] at h
      cases hf : items.foldlM (Pack.append target gap) {} with
      | error e => simp [hf] at h
      | ok result =>
        simp only [hf] at h
        split at h
        · simp at h
        · simp only [Except.ok.injEq] at h
          subst out
          have hp := fold_shelfBefore (by omega : 0 ≤ gap) items
            (s := {}) (by simp [Pack.Inv]) (by simp) hf
          exact List.Pairwise.map (S := shelfBefore)
            (fun r => { r with x := r.x + margin, y := r.y + margin })
            (by intro a b hab; simp only [shelfBefore] at hab ⊢; omega) hp

private theorem packed_shelves_axisSeparated {maxWidth : Nat}
    {gap margin aspectNum aspectDen : Int} {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {i j : Nat} (hne : i ≠ j) {a b frame label : Rect}
    (ha : out.boxes[i]? = some a) (hb : out.boxes[j]? = some b)
    (hf : a.Contained frame) (hl : b.Contained label) : RectAxisSeparated frame label := by
  obtain ⟨hi, ha'⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hb'⟩ := List.getElem?_eq_some_iff.mp hb
  have hp := List.pairwise_iff_getElem.mp (pack_shelfBefore h)
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · have hsep := hp i j hi hj hij
    rw [ha', hb'] at hsep
    simp only [shelfBefore, Rect.Contained, RectAxisSeparated] at hsep hf hl ⊢
    omega
  · have hsep := hp j i hj hi hji
    rw [hb', ha'] at hsep
    simp only [shelfBefore, Rect.Contained, RectAxisSeparated] at hsep hf hl ⊢
    omega

/-- A measured rect emitted by the flat pipeline cannot be strictly inside
a fixed group's frame. All cases follow the actual packed accumulator reads. -/
theorem SceneExecution.measuredRect_not_strictInside_fixedFrame
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry)
    {frame : Box} (hframe : res.scene.boxes[key]? = some frame) (index : Nat) :
    ¬ frame.rect.StrictInside
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.labels.getD index default))) := by
  obtain ⟨_, _, hframeEq⟩ := execution.box_index_origin hframe
  obtain ⟨packed, hpack, hboxes, hlabels, _, _⟩ :=
    packedTransportBounded_of_residuals execution (packedLabelsTransport_of_bridge execution)
  have hkey : key < execution.packedAcc.rects.size := by
    rw [execution.packed_rects_size]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨pk, part, pos, fr, shelf, hpart, hpos, hrect, hshelf, hfr, hcontainFr⟩ :=
    hboxes key hkey _ rfl
  rcases hlabels index _ rfl with
    ⟨pl, labelPart, lr, labelShelf, hlabelPart, hlabel, hlabelShelf, hlr, hcontainLr⟩ | hdefault
  · by_cases heq : pk = pl
    · subst pl
      have hsamePart := Option.some.inj (hlabelPart.symm.trans hpart)
      have hsameShelf := Option.some.inj (hlabelShelf.symm.trans hshelf)
      subst labelPart
      subst labelShelf
      obtain ⟨candidate, run, loops, _, hcomp, hrun, hpartEq⟩ :=
        execution_part_run execution (List.mem_of_getElem? hpart)
      let cg := componentCandidate execution.graph part.1 candidate
      let bd := placeBounds execution.params cg run execution.measured loops
      have hv : pos < part.1.length := (List.getElem?_eq_some_iff.mp hpos).1
      have hv' : pos < cg.nodes.length := by
        simpa [cg, componentCandidate_nodes, componentGraph] using hv
      have hkpos : part.1[pos] = key := (List.getElem?_eq_some_iff.mp hpos).2
      have hsource' : inp.boxes[part.1[pos]]? = some source := by rwa [hkpos]
      have hfr0 : fr = shiftRect (0 - bd.minX) (0 - bd.minY)
          (frameRect execution.params cg run pos) := by
        rw [hpartEq] at hrect
        exact Option.some.inj (hrect.symm.trans
          (placeComponent_rect_get execution.params cg run execution.measured loops hv'))
      have hL : part.2.labels =
          (placedLabels execution.params cg run execution.measured).map
            (fun q => (q.1, shiftRect (0 - bd.minX) (0 - bd.minY) q.2)) := by
        rw [hpartEq]
        exact placeComponent_labels_eq
      rw [hL] at hlabel
      obtain ⟨⟨idx, localLabel⟩, hlocal, hshift⟩ := List.mem_map.mp hlabel
      have hlEq : shiftRect (0 - bd.minX) (0 - bd.minY) localLabel = lr :=
        congrArg Prod.snd hshift
      obtain ⟨measured, edge, e, env, placed, _, _, _, hedge, henv, hstack, hl⟩ :=
        placedLabels_pair_inv (measureLabels_index_nodup execution.measured_eq) hlocal
      have hclear := execution.routeStack_not_strictInside_fixedFrame hwf hframed
        hcomp hrun hv hsource' hfixed hedge henv
        (List.of_mem_zip (List.mem_of_find?_eq_some hstack)).2
      rw [hframeEq]
      dsimp only
      rw [hfr, hlr, hfr0, ← hlEq, hl]
      intro hinside
      exact hclear (strictInside_of_shiftRect (strictInside_of_shiftRect
        (strictInside_of_sceneTransport o.direction hinside)))
    · rw [hframeEq]
      dsimp only
      have hsep := packed_shelves_axisSeparated hpack heq hshelf hlabelShelf hcontainFr hcontainLr
      have hbnd := execution.components_parts_bounded labelPart (List.mem_of_getElem? hlabelPart)
      have hsize := hbnd.2.2.2.2.2 (index, lr) hlabel
      have hdims : 0 ≤ (execution.packedAcc.labels.getD index default).w ∧
          0 ≤ (execution.packedAcc.labels.getD index default).h := by
        rw [hlr]
        exact hsize.2.2.2.2
      intro hinside
      exact not_strictInside_of_separated hsep (Rect.Contained.refl _) hdims.1 hdims.2
        (strictInside_of_sceneTransport o.direction hinside)
  · rw [hdefault]
    exact execution.defaultLabel_not_strictInside (List.mem_of_getElem? hframe)

private theorem title_not_inside_plainFrame
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {i v : Nat} {raw : Rect} {plain : Node}
    (hraw : (i, raw) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some plain)
    (hplain : plain.border = 0)
    (hw : 0 ≤ (transportCaption execution.params o execution.lines comp i raw).w)
    (hh : 0 ≤ (transportCaption execution.params o execution.lines comp i raw).h) :
    ¬ (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).StrictInside
      (transportCaption execution.params o execution.lines comp i raw) := by
  obtain ⟨⟨title, j⟩, hj, hborder, hidx, _, _⟩ :=
    componentTitles_dimension_source _ _ _ hraw
  change i = j at hidx
  subst j
  have htitle := List.mem_zipIdx_iff_getElem?.mp hj
  change title.border = -2 at hborder
  intro hinside
  cases hpath : plain.clusterPath.contains title.decl
  · have hclear := plain_frame_disjoint execution.graph_eq (boxLines_length execution.lines_eq)
      hwf hframed hcomp hrun bracketMarkersAtRank' plainClearOfSideMarker'
      (sideMarkerSpanAligned' (foreignBorderChainXAligned' foreignBorderDivergeStable_framed))
      htitle hnode hborder hplain hpath
    have hself := captionSelfClear_executed execution hcomp hrun hraw htitle hborder
      (captionSelfSidesStrict_executed execution hwf hframed hcomp hrun)
    have hcontainer : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).Contained
        (transportCaption execution.params o execution.lines comp i raw) := by
      simp only [Rect.Contained, Rect.StrictInside] at hself ⊢
      omega
    have hposw : 0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).w := by
      simp only [Rect.StrictInside] at hself
      omega
    have hposh : 0 < (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run i).h := by
      simp only [Rect.StrictInside] at hself
      omega
    exact hclear ((Rect.meetsInterior_comm _ _).mp
      (ownerOverlap_of_caption_inside hcontainer hinside hposw hposh hw hh))
  · obtain ⟨rr, _, hrr, hcoord, _, hranks, _, _⟩ :=
      rankSource_of_componentRun execution.graph_eq hcomp hrun
    obtain ⟨bottom, hbottom⟩ :=
      componentRun_cg_bottom_find execution.graph_eq (boxLines_length execution.lines_eq)
        hcomp htitle hborder
    have hinterv := ranked_compound_member_interval hrr
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitle) hborder hbottom
      (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hplain hpath
    have hit := (List.getElem?_eq_some_iff.mp htitle).1
    have hv := (List.getElem?_eq_some_iff.mp hnode).1
    have hri := prepared_coordinate_original_rk (P := execution.params) (index := i)
      hrr hranks hit
    have hrv := prepared_coordinate_original_rk (P := execution.params) (index := v)
      hrr hranks hv
    rw [hcoord] at hri hrv
    have hi0 := rankWithBudget_rk_nonneg hrr i
    have hlt : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank v).toNat := by
      have hrankLT : rk rr.ranks i < rk rr.ranks v :=
        Int.lt_iff_add_one_le.mpr hinterv.1
      rw [hri, hrv]
      exact (Int.toNat_lt_toNat (Int.lt_of_le_of_lt hi0 hrankLT)).2 hrankLT
    have hi := componentRun_original_nodes_covered hrun i hit
    obtain ⟨member, _, hmember, _, _, _, _, _, _⟩ :=
      componentRun_original_plain_record hrun hnode hplain
    obtain ⟨li, hli, _, _⟩ :=
      run_node_band hrun (List.getElem?_eq_getElem hi)
    obtain ⟨lv, hlv, hvTop, _⟩ := run_node_band hrun hmember
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcoords, _, _⟩ :=
      componentRun_spec hrun
    have hbands := rankAxis_bands_disjoint hcoords _ _ _ _ hlt hli hlv
    have hb := (captionInTopBand_executed execution hcomp hrun hraw htitle hborder).2
    have hliGet : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = li := by
      simp only [List.getD_eq_getElem?_getD, hli, Option.getD_some]
    rw [hliGet] at hb
    have hget : ((componentCandidate execution.graph comp candidate).nodes.getD v default).border
        ≠ -2 := by simp [List.getD_eq_getElem?_getD, hnode, hplain]
    have hframe := plain_frame_eq_boxRect execution.params _ run v
      (List.getElem?_eq_some_iff.mp hmember).1 hget
    have hcaptionTop : (transportCaption execution.params o execution.lines comp i raw).y ≤
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run v).y := by
      rw [hframe, boxRect_top, RouteImpl.yAt]
      exact Int.le_trans (Int.le_add_of_nonneg_right hh)
        (Int.le_trans hb (Int.le_trans hbands hvTop))
    exact Int.not_lt_of_ge hcaptionTop hinside.2.2.1

/-- The substituted title rectangles in `sceneOf` never fit strictly inside
a fixed group, including titles of the group's ancestors. -/
theorem SceneExecution.installedTitle_not_strictInside_fixedFrame
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry)
    {frame : Box} (hframe : res.scene.boxes[key]? = some frame)
    {ownerKey : Nat} {stored : Rect} (hstored : (ownerKey, stored) ∈ execution.packedAcc.titles) :
    let size := titleCaptionSize execution.params o (execution.lines.getD ownerKey [])
    ¬ frame.rect.StrictInside
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          { stored with w := size.w, h := size.h })) := by
  dsimp only
  obtain ⟨_, _, hframeEq⟩ := execution.box_index_origin hframe
  obtain ⟨packed, hpack, hboxes, _, htitles, _⟩ :=
    packedTransportBounded_of_residuals execution (packedLabelsTransport_of_bridge execution)
  have hkey : key < execution.packedAcc.rects.size := by
    rw [execution.packed_rects_size]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨pk, part, pos, fr, shelf, hpart, hpos, hrect, hshelf, hfr, hcontainFr⟩ :=
    hboxes key hkey _ rfl
  obtain ⟨pt, titlePart, i, tr, titleShelf, htitlePart, hi, htitle, htitleShelf, htr, hcontainTr⟩ :=
    htitles ownerKey stored hstored
  by_cases heq : pk = pt
  · subst pt
    have hsamePart := Option.some.inj (htitlePart.symm.trans hpart)
    have hsameShelf := Option.some.inj (htitleShelf.symm.trans hshelf)
    subst titlePart
    subst titleShelf
    obtain ⟨candidate, run, loops, _, hcomp, hrun, hpartEq⟩ :=
      execution_part_run execution (List.mem_of_getElem? hpart)
    let cg := componentCandidate execution.graph part.1 candidate
    let bd := placeBounds execution.params cg run execution.measured loops
    have hv : pos < part.1.length := (List.getElem?_eq_some_iff.mp hpos).1
    have hv' : pos < cg.nodes.length := by simpa [cg, componentCandidate_nodes, componentGraph] using hv
    have hkpos : part.1[pos] = key := (List.getElem?_eq_some_iff.mp hpos).2
    have hsource' : inp.boxes[part.1[pos]]? = some source := by rwa [hkpos]
    obtain ⟨plain, hnode, hplain⟩ := execution.fixed_candidate_node_border_zero
      part.1 candidate pos hv hsource' hfixed
    have hfr0 : fr = shiftRect (0 - bd.minX) (0 - bd.minY)
        (frameRect execution.params cg run pos) := by
      rw [hpartEq] at hrect
      exact Option.some.inj (hrect.symm.trans
        (placeComponent_rect_get execution.params cg run execution.measured loops hv'))
    have hT : part.2.titles = (componentTitles execution.params cg run).map
        (fun q => (q.1, shiftRect (0 - bd.minX) (0 - bd.minY) q.2)) := by
      rw [hpartEq] <;> rfl
    rw [hT] at htitle
    obtain ⟨⟨j, raw⟩, hraw, hshift⟩ := List.mem_map.mp htitle
    have hji : j = i := congrArg Prod.fst hshift
    subst j
    have htr0 : shiftRect (0 - bd.minX) (0 - bd.minY) raw = tr :=
      congrArg Prod.snd hshift
    have hcap : transportCaption execution.params o execution.lines part.1 i raw =
        { raw with
          w := (titleCaptionSize execution.params o (execution.lines.getD ownerKey [])).w
          h := (titleCaptionSize execution.params o (execution.lines.getD ownerKey [])).h } := by
      simp [transportCaption, transportCapSize, List.getD_eq_getElem?_getD, hi]
    have hfit := execution.packed_title_caption_fit (ownerKey, stored) hstored
    have hclear := title_not_inside_plainFrame execution hwf hframed hcomp hrun hraw
      hnode hplain (by rw [hcap]; exact hfit.1) (by rw [hcap]; exact hfit.2.1)
    rw [hcap] at hclear
    rw [hframeEq]
    dsimp only
    rw [hfr, hfr0, htr, ← htr0, captionResize_shift_comm, captionResize_shift_comm]
    intro hinside
    exact hclear (strictInside_of_shiftRect (strictInside_of_shiftRect
      (strictInside_of_sceneTransport o.direction hinside)))
  · rw [hframeEq]
    dsimp only
    have hsep := packed_shelves_axisSeparated hpack heq hshelf htitleShelf hcontainFr hcontainTr
    have hfit := execution.packed_title_caption_fit (ownerKey, stored) hstored
    have htitleRect : { stored with
        w := (titleCaptionSize execution.params o (execution.lines.getD ownerKey [])).w
        h := (titleCaptionSize execution.params o (execution.lines.getD ownerKey [])).h } =
        shiftRect titleShelf.x titleShelf.y { tr with
          w := (titleCaptionSize execution.params o (execution.lines.getD ownerKey [])).w
          h := (titleCaptionSize execution.params o (execution.lines.getD ownerKey [])).h } := by
      rw [htr] <;> rfl
    rw [htitleRect]
    intro hinside
    exact not_strictInside_of_separated hsep (Rect.Contained.refl _) hfit.1 hfit.2.1
      (strictInside_of_sceneTransport o.direction hinside)

private theorem plainFrames_axisSeparated
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {u v : Nat} {nu nv : Node}
    (hu : (componentCandidate execution.graph comp candidate).nodes[u]? = some nu)
    (hv : (componentCandidate execution.graph comp candidate).nodes[v]? = some nv)
    (hnu : nu.border = 0) (hnv : nv.border = 0) (hne : u ≠ v) :
    RectAxisSeparated
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run u)
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run v) := by
  obtain ⟨pu, hcu, hpu, _, hbu, _, _, _, _⟩ := componentRun_original_plain_record hrun hu hnu
  obtain ⟨pv, hcv, hpv, _, hbv, _, _, _, _⟩ := componentRun_original_plain_record hrun hv hnv
  have huP := (List.getElem?_eq_some_iff.mp hpu).1
  have hvP := (List.getElem?_eq_some_iff.mp hpv).1
  have hfu := plain_frame_eq_boxRect execution.params
    (componentCandidate execution.graph comp candidate) run u huP (by
      simp [List.getD_eq_getElem?_getD, hu, hnu])
  have hfv := plain_frame_eq_boxRect execution.params
    (componentCandidate execution.graph comp candidate) run v hvP (by
      simp [List.getD_eq_getElem?_getD, hv, hnv])
  rw [hfu, hfv]
  obtain ⟨lu, hlu, hulo, huhi⟩ := run_node_band hrun hpu
  obtain ⟨lv, hlv, hvlo, hvhi⟩ := run_node_band hrun hpv
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hlanes, _, hcoords, _, _⟩ :=
    componentRun_spec hrun
  let ru := (rk run.coordinateProper.rank u).toNat
  let rv := (rk run.coordinateProper.rank v).toNat
  have hlu' : run.layers[ru]? = some lu := hlu
  have hlv' : run.layers[rv]? = some lv := hlv
  rcases Nat.lt_trichotomy ru rv with hlt | heq | hgt
  · have hbands := rankAxis_bands_disjoint hcoords _ _ _ _ hlt hlu' hlv'
    simp only [RectAxisSeparated, boxRect_top, boxRect_h, RouteImpl.yAt]
    dsimp only [ru, rv] at hbands
    omega
  · have hranks : run.proper.rank = run.coordinateProper.rank := by
      rw [← hdrop, OrderImpl.dropSynthetic_rank]
      exact (proxyWidths_rel hproxy).2.1
    have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
    obtain ⟨layerU, hLayerU, huMem, _⟩ := hcov u huP
    obtain ⟨layerV, hLayerV, hvMem, _⟩ := hcov v hvP
    rw [hranks] at hLayerU hLayerV
    change run.layers[ru]? = some layerU at hLayerU
    change run.layers[rv]? = some layerV at hLayerV
    rw [heq, hLayerV] at hLayerU
    have hsameLayer := Option.some.inj hLayerU
    rw [← hsameLayer] at huMem
    obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp huMem
    obtain ⟨pj, hpj⟩ := List.mem_iff_getElem?.mp hvMem
    have hneq : pi ≠ pj := by
      intro hp
      rw [hp] at hpi
      exact hne (Option.some.inj (hpi.symm.trans hpj))
    have hmem : layerV ∈ run.layers := List.mem_of_getElem? hLayerV
    rcases Nat.lt_or_gt_of_ne hneq with hij | hji
    · have hsep := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun
        hmem hij hpi hpj hcu hcv (by simp [hbu]) (by simp [hbv])
      exact Or.inl (by simpa only [boxRect_left, boxRect_w, RouteImpl.leftOf] using hsep)
    · have hsep := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun
        hmem hji hpj hpi hcv hcu (by simp [hbv]) (by simp [hbu])
      exact Or.inr (Or.inl (by simpa only [boxRect_left, boxRect_w, RouteImpl.leftOf] using hsep))
  · have hbands := rankAxis_bands_disjoint hcoords _ _ _ _ hgt hlv' hlu'
    simp only [RectAxisSeparated, boxRect_top, boxRect_h, RouteImpl.yAt]
    dsimp only [ru, rv] at hbands
    omega

private theorem SceneExecution.plainSource_candidate
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (comp : List Nat) (candidate v key : Nat)
    (hkey : comp[v]? = some key) {source : ModelBox}
    (hsource : inp.boxes[key]? = some source)
    (hplain : source.role = .node ∨ inp.fixedSizes.any (fun e => e.1 == source.id) = true) :
    ∃ node, (componentCandidate execution.graph comp candidate).nodes[v]? = some node ∧
      node.border = 0 := by
  have hlen : key < execution.lines.length := by
    rw [boxLines_length execution.lines_eq]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨node, hnode, hzero⟩ := ownerRes_node_border_zero execution hsource hplain hlen
  refine ⟨node, ?_, hzero⟩
  rw [componentCandidate_nodes]
  change (comp.map (fun k => execution.graph.nodes.getD k default))[v]? = some node
  simp only [List.getElem?_map, hkey, Option.map_some,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

private theorem SceneExecution.plainSources_axisSeparated
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {key ownerKey : Nat}
    {source ownerSource : ModelBox}
    (hsource : inp.boxes[key]? = some source) (hownerSource : inp.boxes[ownerKey]? = some ownerSource)
    (hplain : source.role = .node ∨ inp.fixedSizes.any (fun e => e.1 == source.id) = true)
    (hownerPlain : ownerSource.role = .node ∨ inp.fixedSizes.any (fun e => e.1 == ownerSource.id) = true)
    (hne : key ≠ ownerKey)
    {frame owner : Box} (hframe : res.scene.boxes[key]? = some frame)
    (howner : res.scene.boxes[ownerKey]? = some owner) :
    RectAxisSeparated frame.rect owner.rect := by
  obtain ⟨_, _, hframeEq⟩ := execution.box_index_origin hframe
  obtain ⟨_, _, hownerEq⟩ := execution.box_index_origin howner
  obtain ⟨packed, hpack, hboxes, _, _, _⟩ :=
    packedTransportBounded_of_residuals execution (packedLabelsTransport_of_bridge execution)
  have hbound (i : Nat) (b : ModelBox) (hi : inp.boxes[i]? = some b) :
      i < execution.packedAcc.rects.size := by
    rw [execution.packed_rects_size]
    exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨pf, partF, i, fr, shelfF, hpartF, hi, hfr, hshelfF, hpackedFr, hcontainFr⟩ :=
    hboxes key (hbound _ _ hsource) _ rfl
  obtain ⟨po, partO, j, rr, shelfO, hpartO, hj, hrr, hshelfO, hpackedRr, hcontainRr⟩ :=
    hboxes ownerKey (hbound _ _ hownerSource) _ rfl
  rw [hframeEq, hownerEq]
  dsimp only
  by_cases heq : pf = po
  · subst po
    have hsamePart := Option.some.inj (hpartO.symm.trans hpartF)
    have hsameShelf := Option.some.inj (hshelfO.symm.trans hshelfF)
    subst partO
    subst shelfO
    obtain ⟨candidate, run, loops, _, hcomp, hrun, hpartEq⟩ :=
      execution_part_run execution (List.mem_of_getElem? hpartF)
    let cg := componentCandidate execution.graph partF.1 candidate
    let bd := placeBounds execution.params cg run execution.measured loops
    have hframeAt (pos : Nat) (localRect : Rect) (hpos : partF.2.rects[pos]? = some localRect) :
        localRect = shiftRect (0 - bd.minX) (0 - bd.minY)
          (frameRect execution.params cg run pos) := by
      rw [hpartEq] at hpos
      have hlen := (List.getElem?_eq_some_iff.mp hpos).1
      rw [placeComponent_rects_length] at hlen
      exact Option.some.inj (hpos.symm.trans
        (placeComponent_rect_get execution.params cg run execution.measured loops hlen))
    have hfr' := hframeAt i fr hfr
    have hrr' := hframeAt j rr hrr
    obtain ⟨a, ha, haz⟩ := execution.plainSource_candidate partF.1 candidate i key hi hsource hplain
    obtain ⟨b, hb, hbz⟩ := execution.plainSource_candidate partF.1 candidate j ownerKey hj
      hownerSource hownerPlain
    have hij : i ≠ j := by
      intro h
      rw [h] at hi
      exact hne (Option.some.inj (hi.symm.trans hj))
    have hsep := plainFrames_axisSeparated execution hcomp hrun ha hb haz hbz hij
    rw [hpackedFr, hpackedRr, hfr', hrr']
    exact axisSeparated_shiftRect (axisSeparated_orientRect o.direction
      (axisSeparated_shiftRect (axisSeparated_shiftRect hsep)))
  · have hsep :=
      packed_shelves_axisSeparated hpack heq hshelfF hshelfO hcontainFr hcontainRr
    exact axisSeparated_shiftRect (axisSeparated_orientRect o.direction hsep)

private theorem SceneExecution.fallback_not_strictInside_fixedFrame
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfit : InputFixedFit inp o)
    {key ownerKey : Nat} {source ownerSource : ModelBox} {frame owner : Box}
    (hsource : inp.boxes[key]? = some source)
    (hfixed : inp.fixedSizes.any (fun e => e.1 == source.id) = true)
    (hframe : res.scene.boxes[key]? = some frame)
    (hownerSource : inp.boxes[ownerKey]? = some ownerSource)
    (howner : res.scene.boxes[ownerKey]? = some owner)
    (hex : ownerSource.exclusive = false)
    (howned : ∃ l ∈ inp.labels, l.owner = ownerSource.id)
    (hnone : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == ownerSource.id) = none)
    (hne : key ≠ ownerKey) :
    ¬ frame.rect.StrictInside (ownedTextRect execution.params owner (execution.lines.getD ownerKey [])) := by
  have hsep := execution.plainSources_axisSeparated hsource hownerSource (Or.inr hfixed)
    (execution.fallback_owner_cases hwf hownerSource hnone) hne hframe howner
  have hcontain := Elegant.Layered.ownerCaptionContainFallback_of_fit hwf hfit
    execution ownerKey ownerSource hownerSource hnone hex howned
  have hm := howner
  rw [execution.boxes_eq_map] at hm
  change (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerKey]? = some owner at hm
  simp only [List.getD_eq_getElem?_getD, hm, Option.getD_some] at hcontain
  obtain ⟨_, _, horigin⟩ := execution.box_index_origin howner
  have hbounded : Size.containsCellRect res.scene.canvas owner.rect = true := by
    rw [horigin]
    exact execution.owner_rect_bounded ownerKey
  simp only [Size.containsCellRect, decide_eq_true_iff] at hbounded
  have hdim : 0 ≤ (ownedTextRect execution.params owner (execution.lines.getD ownerKey [])).w ∧
      0 ≤ (ownedTextRect execution.params owner (execution.lines.getD ownerKey [])).h := by
    unfold ownedTextRect
    split
    · unfold titleRect
      exact ⟨Int.le_max_left _ _, Int.mul_nonneg (by omega) execution.parameter_signs.1⟩
    · exact ⟨hbounded.2.2.1, Int.mul_nonneg (Int.natCast_nonneg _) execution.parameter_signs.1⟩
  exact not_strictInside_of_separated hsep hcontain hdim.1 hdim.2

/-- Successful flat layout cannot place a foreign label strictly inside a
fixed frame. Fit is used only for the box-owned fallback caption. -/
theorem flatFixedFrameLabel_not_strictInside
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hfit : InputFixedFit inp o) (hrun : layout inp o = .ok res)
    {id : String} {frame : Box} {label : SceneLabel}
    (hfixed : ∃ size, (id, size) ∈ inp.fixedSizes)
    (hlookup : res.scene.boxes.find? (fun box => box.id == id) = some frame)
    (hlabel : label ∈ res.scene.labels) (hforeign : label.owner ≠ id) :
    ¬ frame.rect.StrictInside label.rect := by
  obtain ⟨execution⟩ := layout_sceneExecution hrun
  obtain ⟨key, hframe⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hlookup)
  obtain ⟨source, hsource, hframeEq⟩ := execution.box_index_origin hframe
  have hframeId : frame.id = id := by simpa using List.find?_some hlookup
  have hsourceId : source.id = id := (congrArg Box.id hframeEq).symm.trans hframeId
  obtain ⟨size, hsize⟩ := hfixed
  have hany : inp.fixedSizes.any (fun e => e.1 == source.id) = true :=
    List.any_eq_true.mpr ⟨(id, size), hsize, by simp [hsourceId]⟩
  obtain ⟨entry, hfixed⟩ :
      ∃ entry, inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry := by
    cases hfind : inp.fixedSizes.find? (fun e => e.1 == source.id) with
    | some entry => exact ⟨entry, rfl⟩
    | none =>
      have hfalse := (List.find?_eq_none.mp hfind) (id, size) hsize
      simp [hsourceId] at hfalse
  rw [execution.scene_eq] at hlabel
  obtain ⟨⟨original, index⟩, hzip, hemitted⟩ := List.mem_filterMap.mp hlabel
  have hlabelSource := List.mem_zipIdx_iff_getElem?.mp hzip
  cases hexclusive : inp.boxes.any (fun box => box.id == original.owner && box.exclusive) with
  | true => simp only [hexclusive, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == index) with
    | some measured =>
      simp only [hm] at hemitted
      have hrect := congrArg (fun s : SceneLabel => s.rect) (Option.some.inj hemitted)
      change (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.straightAcc.canvasH
          (execution.straightAcc.labels.getD measured.index default))) = label.rect at hrect
      rw [execution.straight_canvasH, (Elegant.Layered.PipelineImpl.straightenAcc_fields execution.straight_eq).2.1] at hrect
      rw [← hrect]
      exact execution.measuredRect_not_strictInside_fixedFrame hwf hframed hsource hfixed
        hframe measured.index
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box => box.id == original.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerKey =>
        simp only [ho] at hemitted
        have hlabelEq := Option.some.inj hemitted
        have hlabelOwner : original.owner = label.owner :=
          congrArg (fun s : SceneLabel => s.owner) hlabelEq
        have hrect := congrArg (fun s : SceneLabel => s.rect) hlabelEq
        change sceneCaptionRect execution.params inp o execution.lines execution.straightAcc
          ownerKey original.owner = label.rect at hrect
        have hcapBridge : sceneCaptionRect execution.params inp o execution.lines
            execution.straightAcc ownerKey original.owner =
            sceneCaptionRect execution.params inp o execution.lines
            execution.packedAcc ownerKey original.owner := by
          unfold sceneCaptionRect sceneTitlesExpr sceneBoxesExpr
          rw [execution.straight_titles, execution.straight_canvasH,
            (Elegant.Layered.PipelineImpl.straightenAcc_fields execution.straight_eq).1]
        rw [hcapBridge] at hrect
        unfold sceneCaptionRect at hrect
        cases ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
            (fun title => title.1 == original.owner) with
        | some title =>
          obtain ⟨⟨titleKey, stored⟩, hstored, htitleEq⟩ :=
            List.mem_filterMap.mp (List.mem_of_find?_eq_some ht)
          cases hb : inp.boxes[titleKey]? with
          | none => simp only [hb] at htitleEq; cases htitleEq
          | some _ =>
            simp only [hb] at htitleEq
            have htitleRect := congrArg Prod.snd (Option.some.inj htitleEq)
            simp only [ht, Option.map_some, Option.getD_some] at hrect
            rw [← hrect, ← htitleRect]
            exact execution.installedTitle_not_strictInside_fixedFrame hwf hframed hsource
              hfixed hframe hstored
        | none =>
          obtain ⟨hb, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
          let ownerSource := inp.boxes[ownerKey]'hb
          have hownerSource : inp.boxes[ownerKey]? = some ownerSource := List.getElem?_eq_getElem hb
          have hownerId : ownerSource.id = original.owner := hp.1
          have hne : key ≠ ownerKey := by
            intro heq
            rw [heq, hownerSource] at hsource
            have hob := Option.some.inj hsource
            exact hforeign (hlabelOwner.symm.trans (hownerId.symm.trans
              ((congrArg ModelBox.id hob).trans hsourceId)))
          have hlen : (sceneBoxesExpr execution.params inp o execution.packedAcc).length =
              inp.boxes.length := by simp [sceneBoxesExpr]
          have hpos : ownerKey < (sceneBoxesExpr execution.params inp o execution.packedAcc).length :=
            hlen.symm ▸ hb
          obtain ⟨owner, hownerMap⟩ :
              ∃ owner, (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerKey]? =
                some owner := ⟨_, List.getElem?_eq_getElem hpos⟩
          have howner : res.scene.boxes[ownerKey]? = some owner := by
            rw [execution.boxes_eq_map]
            exact hownerMap
          have hownerGet : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
              ownerKey ⟨"", "", default, "", false⟩ = owner := by
            simp only [List.getD_eq_getElem?_getD, hownerMap, Option.getD_some]
          simp only [ht, Option.map_none, Option.getD_none, hownerGet] at hrect
          rw [← hrect]
          apply execution.fallback_not_strictInside_fixedFrame hwf hfit hsource hany hframe
            hownerSource howner hp.2
          · exact ⟨original, List.mem_of_getElem? hlabelSource, hownerId.symm⟩
          · rwa [hownerId]
          · exact hne

/-- The fit premise for the flat obstruction transports from the input at
the root of the actual descent; no predicate on the resulting scene is needed. -/
theorem flatFixedFrameLabel_not_strictInside_of_top_fit
    {root inp : Input} {top o : Options} {res : FamilyResult}
    (hreached : FitReached root top inp o) (htop : InputFixedFit root top)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hrun : layout inp o = .ok res)
    {id : String} {frame : Box} {label : SceneLabel}
    (hfixed : ∃ size, (id, size) ∈ inp.fixedSizes)
    (hlookup : res.scene.boxes.find? (fun box => box.id == id) = some frame)
    (hlabel : label ∈ res.scene.labels) (hforeign : label.owner ≠ id) :
    ¬ frame.rect.StrictInside label.rect :=
  flatFixedFrameLabel_not_strictInside hwf hframed (fitPerCall_of_top htop hreached)
    hrun hfixed hlookup hlabel hforeign

end Elegant.Layered.PipelineImpl
