import Elegant.Layered.RegionReservedChildTransfer
import Elegant.Layered.RegionC8aGroupPlain
import Elegant.Layered.RegionPartSizingClosed
import Elegant.Layered.RunLocalSeparationsProof

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem forward_chainUp_rooted_aux {rm : ComponentRegions} {pl : RegionPlacement}
    {resolve : Nat → Nat}
    (hchildren : ∀ a b, b ∈ pl.children.getD a [] →
      b < rm.clusters.length ∧ parentGroup rm b = a)
    (path : List Nat) {start fuel : Nat} {acc : List Nat}
    (hpath : GroupPlainRootedPath pl resolve start path) :
    chainUp rm rm.clusters.length (path.length + fuel)
        ((path.map resolve).getLast?.getD start) acc =
      chainUp rm rm.clusters.length fuel start (path.map resolve ++ acc) := by
  induction path generalizing start fuel acc with
  | nil => simp
  | cons d ds ih =>
    change resolve d ∈ pl.children.getD start [] ∧ GroupPlainRootedPath pl resolve (resolve d) ds at hpath
    obtain ⟨hlt, hparent⟩ := hchildren start (resolve d) hpath.1
    have hlen : (d :: ds).length + fuel = ds.length + (fuel + 1) := by
      simp only [List.length_cons]
      omega
    rw [hlen, List.map_cons, List.getLast?_cons, Option.getD_some, ih hpath.2]
    simp only [chainUp, beq_iff_eq, ite_eq_right (Nat.ne_of_lt hlt), hparent, List.cons_append]

theorem forward_chainUp_rooted {rm : ComponentRegions} {pl : RegionPlacement}
    {resolve : Nat → Nat}
    (hchildren : ∀ a b, b ∈ pl.children.getD a [] →
      b < rm.clusters.length ∧ parentGroup rm b = a)
    {path : List Nat} (hpath : GroupPlainRootedPath pl resolve rm.clusters.length path)
    (hlen : path.length ≤ rm.clusters.length) :
    chainUp rm rm.clusters.length (rm.clusters.length + 1)
      ((path.map resolve).getLast?.getD rm.clusters.length) [] = path.map resolve := by
  have hfuel : rm.clusters.length + 1 = path.length + ((rm.clusters.length - path.length) + 1) := by
    omega
  rw [hfuel, forward_chainUp_rooted_aux hchildren path hpath]
  simp [chainUp]

private theorem forward_rooted_prefix {pl : RegionPlacement} {resolve : Nat → Nat}
    (pref rest : List Nat) {g : Nat}
    (h : GroupPlainRootedPath pl resolve g (pref ++ rest)) :
    GroupPlainRootedPath pl resolve g pref := by
  induction pref generalizing g with
  | nil => trivial
  | cons d ds ih => exact ⟨h.1, ih h.2⟩

private theorem forward_filter_common (a b : List Nat)
    (hagrees : ∀ x pa pb ra rb, a = pa ++ x :: ra → b = pb ++ x :: rb → pa = pb) :
    b.filter (fun x => a.contains x) = OrderImpl.commonPath a b := by
  induction b generalizing a with
  | nil => cases a <;> rfl
  | cons y ys ih =>
    cases a with
    | nil => simp [OrderImpl.commonPath]
    | cons x xs =>
      by_cases hxy : x = y
      · subst y
        have hp : ∀ z ∈ ys, (x :: xs).contains z = xs.contains z := by
          intro z hz
          by_cases hx : z = x
          · subst z
            obtain ⟨p, r, he⟩ := List.mem_iff_append.mp hz
            have hh : ([] : List Nat) = x :: p :=
              hagrees x [] (x :: p) xs r rfl (by rw [he, List.cons_append])
            cases hh
          · rw [List.contains_cons]
            simp [hx]
        have hc : ys.filter (fun z => (x :: xs).contains z) =
            ys.filter (fun z => xs.contains z) := List.filter_congr hp
        have hrec := ih xs (by
          intro z pa pb ra rb ha hb
          exact (List.cons.inj (hagrees z (x :: pa) (x :: pb) ra rb
            (by rw [ha, List.cons_append]) (by rw [hb, List.cons_append]))).2)
        simp only [List.filter_cons_of_pos (by simp : (x :: xs).contains x = true),
          hc, hrec, OrderImpl.commonPath, ite_true]
      · rw [OrderImpl.commonPath, ite_eq_right hxy, List.filter_eq_nil_iff]
        intro z hz ha
        obtain ⟨pa, ra, ha'⟩ := List.mem_iff_append.mp (List.contains_iff_mem.mp ha)
        obtain ⟨pb, rb, hb'⟩ := List.mem_iff_append.mp hz
        have hp := hagrees z pa pb ra rb ha' hb'
        subst pb
        have hfirst : (pa ++ z :: ra).head? = (pa ++ z :: rb).head? := by
          cases pa <;> rfl
        rw [← ha', ← hb'] at hfirst
        simp only [List.head?_cons] at hfirst
        exact hxy (Option.some.inj hfirst)

theorem forward_edgeOwner_of_resolved_paths {rm : ComponentRegions} {pl : RegionPlacement}
    {groups : List Nat} {tail head : Nat} {a b : List Nat}
    (hchildren : ∀ x y, y ∈ pl.children.getD x [] →
      y < rm.clusters.length ∧ parentGroup rm y = x)
    (ha : GroupPlainRootedPath pl id rm.clusters.length a)
    (hb : GroupPlainRootedPath pl id rm.clusters.length b)
    (hla : a.length ≤ rm.clusters.length) (hlb : b.length ≤ rm.clusters.length)
    (hta : groups.getD tail rm.clusters.length = a.getLast?.getD rm.clusters.length)
    (htb : groups.getD head rm.clusters.length = b.getLast?.getD rm.clusters.length) :
    edgeOwnerOf rm groups rm.clusters.length tail head =
      (OrderImpl.commonPath a b).getLast?.getD rm.clusters.length := by
  have hagrees : ∀ x pa pb ra rb, a = pa ++ x :: ra → b = pb ++ x :: rb → pa = pb := by
    intro x pa pb ra rb hap hbp
    have har : GroupPlainRootedPath pl id rm.clusters.length ((pa ++ [x]) ++ ra) := by
      simpa only [List.append_assoc, List.singleton_append, ← hap] using ha
    have hbr : GroupPlainRootedPath pl id rm.clusters.length ((pb ++ [x]) ++ rb) := by
      simpa only [List.append_assoc, List.singleton_append, ← hbp] using hb
    have hapLen : (pa ++ [x]).length ≤ rm.clusters.length := by
      rw [hap, List.length_append, List.length_cons] at hla
      simp only [List.length_append, List.length_singleton]
      omega
    have hbpLen : (pb ++ [x]).length ≤ rm.clusters.length := by
      rw [hbp, List.length_append, List.length_cons] at hlb
      simp only [List.length_append, List.length_singleton]
      omega
    have hpa := forward_chainUp_rooted hchildren (forward_rooted_prefix _ _ har) hapLen
    have hpb := forward_chainUp_rooted hchildren (forward_rooted_prefix _ _ hbr) hbpLen
    simp only [List.map_id, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.getD_some] at hpa hpb
    exact List.append_cancel_right (hpa.symm.trans hpb)
  unfold edgeOwnerOf
  have htail := forward_chainUp_rooted hchildren ha hla
  have hhead := forward_chainUp_rooted hchildren hb hlb
  simp only [List.map_id] at htail hhead
  rw [hta, htb, htail, hhead]
  change (b.reverse.find? (fun g => a.contains g)).getD rm.clusters.length = _
  rw [← List.getLast?_filter, forward_filter_common _ _ hagrees]

private theorem forward_rooted_map {pl : RegionPlacement} {resolve : Nat → Nat}
    {start : Nat} {path : List Nat} (h : GroupPlainRootedPath pl resolve start path) :
    GroupPlainRootedPath pl id start (path.map resolve) := by
  induction path generalizing start with
  | nil => trivial
  | cons d ds ih => exact ⟨h.1, ih h.2⟩

private theorem forward_commonPath_map (resolve : Nat → Nat) (a b : List Nat)
    (hinj : ∀ x ∈ a, ∀ y ∈ b, resolve x = resolve y → x = y) :
    OrderImpl.commonPath (a.map resolve) (b.map resolve) =
      (OrderImpl.commonPath a b).map resolve := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        have hrec := ih ys (by
          intro a ha b hb
          exact hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        simp only [List.map_cons, OrderImpl.commonPath, ite_true, hrec]
      · have hne : resolve x ≠ resolve y :=
          fun he => hxy (hinj x List.mem_cons_self y List.mem_cons_self he)
        simp only [List.map_cons, OrderImpl.commonPath, ite_eq_right hxy, ite_eq_right hne,
          List.map_nil]

theorem forward_edgeOwner_of_decl_paths {rm : ComponentRegions} {pl : RegionPlacement}
    {resolve : Nat → Nat} {groups : List Nat} {tail head : Nat} {a b : List Nat}
    (hchildren : ∀ x y, y ∈ pl.children.getD x [] →
      y < rm.clusters.length ∧ parentGroup rm y = x)
    (ha : GroupPlainRootedPath pl resolve rm.clusters.length a)
    (hb : GroupPlainRootedPath pl resolve rm.clusters.length b)
    (hla : a.length ≤ rm.clusters.length) (hlb : b.length ≤ rm.clusters.length)
    (hinj : ∀ x ∈ a, ∀ y ∈ b, resolve x = resolve y → x = y)
    (hta : groups.getD tail rm.clusters.length = (a.map resolve).getLast?.getD rm.clusters.length)
    (htb : groups.getD head rm.clusters.length = (b.map resolve).getLast?.getD rm.clusters.length) :
    edgeOwnerOf rm groups rm.clusters.length tail head =
      ((OrderImpl.commonPath a b).map resolve).getLast?.getD rm.clusters.length := by
  rw [← forward_commonPath_map resolve a b hinj]
  exact forward_edgeOwner_of_resolved_paths hchildren (forward_rooted_map ha) (forward_rooted_map hb)
    (by simpa only [List.length_map] using hla) (by simpa only [List.length_map] using hlb) hta htb

private abbrev forwardAnchorRank (run : Run) (e : Edge) : Int :=
  rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2

private theorem forward_placed_anchor_right {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {candidate cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {options : OrderOptions}
    (hrun : componentRunR P exact spec inp candidate labels options = .ok (cg, run))
    {index edge : Nat} {rect : Rect} {source : MeasuredLabel} {e : Edge}
    (hmem : (index, rect) ∈ placedLabels P cg run labels)
    (huniq : (labels.map (·.index)).Nodup)
    (hsource : source ∈ labels) (hindex : source.index = index)
    (hfind : cg.edges.findIdx? (fun x => x.decl == source.edge) = some edge)
    (hedge : cg.edges[edge]? = some e) (hne : e.tail ≠ e.head) (hforward : e.reversed = false) :
    ∃ v nd, labelAnchorIndex run.proper edge (forwardAnchorRank run e) = some v ∧
      run.proper.nodes[v]? = some nd ∧
      rect.x + rect.w ≤ run.xs.getD v 0 - Int.fdiv nd.node.w 2 + nd.node.w := by
  obtain ⟨ml, edge', e', env, picked, hml, hmlIndex, hfind', hedge', henv, hstack, hrect⟩ :=
    placedLabels_pair_inv huniq hmem
  have hmlEq := measured_eq_of_index_eq labels huniq ml source hml hsource
    (hmlIndex.trans hindex.symm)
  subst ml
  have heIndex := Option.some.inj (hfind'.symm.trans hfind)
  subst edge'
  have he := Option.some.inj (hedge'.symm.trans hedge)
  subst e'
  obtain ⟨first, q, hfirst, hq, henvEq⟩ := forward_envelope_eq hne hforward henv
  obtain ⟨v, nd, hv, hnd, hw, _⟩ := componentRunR_forward_anchor_size hrun hedge hne hfirst
  have hqIndex : q.2 = v := by
    have h := hv
    rw [labelAnchorIndex_eq] at h
    simpa only [hq, Option.map_some, Option.some.injEq] using h
  have hmember := (List.of_mem_zip (List.mem_of_find?_eq_some hstack)).2
  have hright := (Labels.stackRects_width_le env.x cg.slot _ env.y picked hmember).2
  rw [henvEq, hqIndex] at hright
  simp only [Labels.textRectAt, Labels.rectAt, Labels.labelRect, RouteImpl.xAt,
    RouteImpl.nodeW, hnd] at hright
  rw [stackSize_width_eq] at hw
  refine ⟨v, nd, hv, hnd, ?_⟩
  rw [hrect]
  omega

private theorem forward_anchor_bucket_right {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper}
    {minimum : RegionConstraints} {layers pinned : List (List Nat)}
    {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hparents : rm.parents.length = rm.clusters.length) (hmin : constrainR rm P p = .ok minimum)
    {v owner : Nat} {nd : ProperNode} {run : Run}
    (hpre : p.nodes[v]? = some nd) (hborder : nd.node.border = 0)
    (howner : stages.groups[v]? = some owner) (hbound : owner ≤ rm.clusters.length)
    (hcenter : run.xs.getD v 0 = stages.shifted.getD v 0) :
    run.xs.getD v 0 - Int.fdiv nd.node.w 2 + nd.node.w ≤
      groupPlain_bucketRight stages.placement P stages.allocation owner := by
  obtain ⟨hm, hmove⟩ := groupPlain_shifted_center stages hparents hmin hpre hborder howner hbound
  have hright := (stages.bucket_width_and_hull.2 owner v hm).2
  have hpl : stages.placement.p = p := by rw [stages.hPlacement]
  have hn : stages.placement.p.nodes[v]? = some nd := by rwa [hpl]
  have hsize := CoordsImpl.nodeW_nonneg
    (CoordsImpl.crossCoordsClusterWith_spec stages.hCross).2.2.2.1 v
  have htotal : 0 ≤ nd.node.w + 2 * (nd.node.loopExtent : Int) := by
    simpa only [CoordsImpl.nodeW, hpre] using hsize
  have hhalf : Int.tdiv (nd.node.w + 2 * (nd.node.loopExtent : Int)) 2 =
      nd.node.w / 2 + (nd.node.loopExtent : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg htotal]
    exact Int.add_mul_ediv_left nd.node.w (nd.node.loopExtent : Int) (by decide)
  have hfloor := Int.fdiv_eq_ediv_of_nonneg nd.node.w (b := 2) (by decide)
  have hextent : 0 ≤ (nd.node.loopExtent : Int) := Int.natCast_nonneg _
  simp only [CoordsImpl.nodeW, hn, hhalf] at hright
  unfold groupPlain_bucketRight
  rw [hcenter, hmove, hfloor]
  omega

/-- The remaining bridge is the anchor's record, allocation center and owner lookup.
It has no rectangle-clearance, containment or validator conclusion. -/
def R8b_ForwardAnchorBucketTrace (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part),
    WellFormed (inputModel inp o) → framedParents inp = true →
    part.1 ∈ components execution.graph →
    ∀ {s : RegionSpec} {rm : ComponentRegions} {ranks : List Int} {budget : Bool}
      {p0 labeled p : Proper} {minimum : RegionConstraints} {ord : OrderResult}
      {reserved : List (Option Int)},
      selected.spec = some s →
      newComponentRegions (some s) execution.params inp
        (componentCandidateR (some s) execution.graph part.1 selected.candidate) = .ok (some rm) →
      rankEquivalentR rm (componentCandidateR (some s) execution.graph part.1 selected.candidate) =
        .ok (ranks, selected.cg, budget) →
      normalize selected.cg ranks = .ok p0 →
      Labels.addLabelNodes selected.cg p0 (componentLabels selected.cg execution.measured) = .ok labeled →
      coordinateGraphR execution.params (exactDecls exactIds inp) (some s) labeled = p →
      constrainR rm execution.params p = .ok minimum →
      orderWithBudget p (candidateOrder selected.candidate) = .ok ord →
      ∀ (stages : RegionCrossAllocationStages execution.params rm selected.cg execution.measured
          p minimum ord.layers selected.run.layers selected.run.coordinateXs reserved
          selected.run.coordinateProper)
        {edge v : Nat} {e : Edge} {nd : ProperNode},
        selected.cg.edges[edge]? = some e → e.tail ≠ e.head → e.reversed = false →
        labelAnchorIndex selected.run.proper edge (forwardAnchorRank selected.run e) = some v →
        selected.run.proper.nodes[v]? = some nd →
        p.nodes[v]? = some nd ∧ nd.node.border = 0 ∧
          selected.run.xs.getD v 0 = stages.shifted.getD v 0 ∧
          stages.groups[v]? = some (edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head)

/-- Same actual owner/child lookup as for a reversed edge, but no allocated lane. -/
def R8b_EmittedForwardChildAt {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart execution part) (index pos : Nat) : Prop :=
  ∃ (srcLabel : ModelLabel) (label : MeasuredLabel) (edge : Nat) (e : Edge),
    inp.labels[index]? = some srcLabel ∧
    (inp.boxes.any fun b => b.id == srcLabel.owner && b.exclusive) = false ∧
    execution.measured.find? (fun l => l.index == index) = some label ∧
    selected.cg.edges.findIdx? (fun x => x.decl == label.edge) = some edge ∧
    selected.cg.edges[edge]? = some e ∧ e.tail ≠ e.head ∧ e.reversed = false ∧
    R8b_ActualReservedChildAt selected e pos

set_option maxHeartbeats 4000000 in
private theorem forwardChild_raw_geometry {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (htrace : R8b_ForwardAnchorBucketTrace exactIds idSets)
    (selected : R8b_ChosenPart execution part)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hpart : part ∈ execution.componentsAcc.parts)
    {index pos : Nat} {rect : Rect}
    (hraw : (index, rect) ∈ placedLabels execution.params selected.cg selected.run execution.measured)
    (hbranch : R8b_EmittedForwardChildAt selected index pos) :
    pos < selected.cg.nodes.length ∧ Disjoint (frameRect execution.params selected.cg selected.run pos) rect := by
  obtain ⟨_, label, edge, e, _, _, hfind, heFind, he, hne, hforward, hownerChild⟩ := hbranch
  obtain ⟨s, rm, hspec, hactive, p, groups, children, hp, hgroups, hchildren,
    owner, child, k, c, howner, heOwner, hchild, hc, htop⟩ := hownerChild
  have hrun := selected.run_eq
  rw [hspec] at hrun
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem hpart
  obtain ⟨ranks, p0, labeled, p', minimum, ord, reserved, budget, hrank, hnorm, hlabels,
    hcoord, hmin, hord, ⟨stages⟩⟩ := componentRunR_active_allocation_stages hrun hactive
  have hp' : activeReservedChildCrossInput execution.params (exactDecls exactIds inp) s rm
      (componentCandidateR (some s) execution.graph part.1 selected.candidate)
      execution.measured = .ok p' := by
    unfold activeReservedChildCrossInput
    rw [hrank]
    change (normalize selected.cg ranks).bind (fun q =>
      (Labels.addLabelNodes selected.cg q (componentLabels selected.cg execution.measured)).bind
        (fun l => .ok (coordinateGraphR execution.params (exactDecls exactIds inp) (some s) l))) = .ok p'
    rw [hnorm]
    change (Labels.addLabelNodes selected.cg p0 (componentLabels selected.cg execution.measured)).bind
      (fun l => .ok (coordinateGraphR execution.params (exactDecls exactIds inp) (some s) l)) = .ok p'
    rw [hlabels]
    exact congrArg Except.ok hcoord
  have hpEq : p' = p := Except.ok.inj (hp'.symm.trans hp)
  have hgroups' : nodeGroupsOf rm p' = .ok groups := by rwa [hpEq]
  have hgs : stages.groups = groups := Except.ok.inj (stages.hGroups.symm.trans hgroups')
  have hcs : stages.placement.children = children := by
    rw [stages.hPlacement]
    exact Except.ok.inj (stages.hChildren.symm.trans hchildren)
  have hoa : edgeOwnerOf rm stages.groups rm.clusters.length e.tail e.head = owner := by
    rwa [hgs]
  have hch : (stages.placement.children.getD owner [])[k]? = some child := by
    rwa [hcs]
  have hindex : label.index = index := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  obtain ⟨v, nd, hanchor, hnd, hright⟩ := forward_placed_anchor_right hrun hraw
    (measureLabels_index_nodup execution.measured_eq) (List.mem_of_find?_eq_some hfind)
    hindex heFind he hne hforward
  obtain ⟨hpre, hb, hx, hg⟩ := htrace selected hwf hfp hcomp hspec hactive hrank hnorm hlabels
    hcoord hmin hord stages he hne hforward hanchor hnd
  rw [hoa] at hg
  have hparents := activeRegion_parent_count hactive
  have hlabel := Int.le_trans hright
    (forward_anchor_bucket_right stages hparents hmin hpre hb hg (Nat.le_of_lt howner) hx)
  obtain ⟨frame, hframe, hborder, hdecl⟩ := activeChild_frame_record hactive hrank hc
  rw [htop] at hframe
  have hleftFrame := (stages.activeChild_frame_within_reservation execution.graph0_eq
    execution.graph_eq hcomp hrun hactive hrank hnorm hlabels hcoord execution.checked hmin hc
    hframe hborder hdecl).1
  have hinset : 0 ≤ regionInsetOf execution.params := by
    have hpad := (checkedParams_sizing_nonneg execution.checked).2.1
    have hb := checkedParams_clusterBorderW_ge_one execution.checked
    unfold regionInsetOf
    omega
  obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun stages
  have hw := reserveWidths_nonnegative hinset hown hlane hloop
  have heWidth := groupPlain_allocation_width_eq stages.hAllocation
  have hw' : ∀ g, 0 ≤ stages.allocation.widths.getD g 0 := by rwa [heWidth]
  have hleft := stages.childBudget_left_from_allocation hactive hmin (Nat.le_of_lt howner) hch
  have hroot : stages.placement.rm.clusters.length = rm.clusters.length := by rw [stages.hPlacement]
  have hleft' : groupPlain_allocLeft stages.allocation child =
      groupPlain_bucketRight stages.placement execution.params stages.allocation owner +
        (((stages.placement.children.getD owner []).take k).map fun g =>
          stages.allocation.widths.getD g 0).sum := by
    unfold groupPlain_allocLeft groupPlain_bucketRight groupPlain_bucketLeft
    rw [hroot, heWidth]
    exact hleft
  have hcut := groupPlain_bucket_before_child hw' hleft'
  exact ⟨(List.getElem?_eq_some_iff.mp hframe).1,
    rect_disjoint_of_x (Or.inr (Int.le_trans hlabel (Int.le_trans hcut hleftFrame)))⟩

theorem regionC8b_selectedForwardChild_stored_of_bucketTrace {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (htrace : R8b_ForwardAnchorBucketTrace exactIds idSets)
    (selected : R8b_ChosenPart execution part)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos : Nat} {stored frame : Rect}
    (hstored : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hbranch : R8b_EmittedForwardChildAt selected index pos) :
    ∃ raw, pos < selected.cg.nodes.length ∧
      (index, raw) ∈ placedLabels execution.params selected.cg selected.run execution.measured ∧
      (let b := placeBoundsX execution.params selected.cg selected.run execution.measured selected.loops
       stored = shiftRect (0 - b.minX) (-b.minY) raw) ∧
      Disjoint (frameRect execution.params selected.cg selected.run pos) raw ∧ Disjoint frame stored := by
  let b := placeBoundsX execution.params selected.cg selected.run execution.measured selected.loops
  let translate := shiftRect (0 - b.minX) (-b.minY)
  have hmapped : (index, stored) ∈
      (placedLabels execution.params selected.cg selected.run execution.measured).map
        (fun q => (q.1, translate q.2)) := by
    rw [selected.part_eq] at hstored
    exact hstored
  obtain ⟨⟨idx, raw⟩, hraw, hstore⟩ := List.mem_map.mp hmapped
  change (idx, translate raw) = (index, stored) at hstore
  simp only [Prod.mk.injEq] at hstore
  obtain ⟨hidx, hshift⟩ := hstore
  subst idx
  obtain ⟨hpos, hclear⟩ := forwardChild_raw_geometry htrace selected hwf hfp hpart hraw hbranch
  have hf : part.2.rects[pos]? =
      some (translate (frameRect execution.params selected.cg selected.run pos)) := by
    rw [selected.part_eq]
    unfold placeComponentExact
    change (((List.range selected.cg.nodes.length).map
      (frameRect execution.params selected.cg selected.run)).map translate)[pos]? = _
    simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some]
  refine ⟨raw, hpos, hraw, hshift.symm, hclear, ?_⟩
  rw [Option.some.inj (hframe.symm.trans hf), ← hshift]
  exact disjoint_shiftRect hclear

theorem regionC8b_selectedForwardChild_emitted_of_bucketTrace {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (htrace : R8b_ForwardAnchorBucketTrace exactIds idSets)
    (selected : R8b_ChosenPart execution part)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hpart : part ∈ execution.componentsAcc.parts) {index pos key : Nat}
    {stored frame shelf : Rect} {srcBox : ModelBox}
    (hstored : (index, stored) ∈ part.2.labels) (hframe : part.2.rects[pos]? = some frame)
    (hkey : part.1[pos]? = some key) (hsrc : inp.boxes[key]? = some srcBox)
    (hgroup : srcBox.role = .group)
    (hpackBox : execution.packedAcc.rects.getD key default = shiftRect shelf.x shelf.y frame)
    (hpackLabel : execution.packedAcc.labels.getD index default = shiftRect shelf.x shelf.y stored)
    (hbranch : R8b_EmittedForwardChildAt selected index pos) :
    ∃ (srcLabel : ModelLabel) (g : Box) (l : SceneLabel),
      inp.labels[index]? = some srcLabel ∧ g ∈ res.scene.boxes ∧ l ∈ res.scene.labels ∧
      g.id = srcBox.id ∧ g.role = "group" ∧ l.id = srcLabel.id ∧ Disjoint g.rect l.rect := by
  obtain ⟨raw, hpos, hraw, hshift, hclear, _⟩ :=
    regionC8b_selectedForwardChild_stored_of_bucketTrace htrace selected hwf hfp hpart
      hstored hframe hbranch
  obtain ⟨srcLabel, _, _, _, hsrcLabel, hnotHidden, hfind, _⟩ := hbranch
  obtain ⟨g, l, hg, hl, hid, hrole, hlid, hd⟩ := regionC8b_samePart_emitted_routeLabel_disjoint
    execution (packBox := shelf) selected.part_eq hkey hpos hsrc hgroup hsrcLabel hnotHidden hfind
    hframe hshift (fun _ _ => hpackBox) (fun _ => hpackLabel) hraw hclear
  exact ⟨srcLabel, g, l, hsrcLabel, hg, hl, hid, hrole, hlid, hd⟩

#print axioms forward_chainUp_rooted
#print axioms forward_edgeOwner_of_resolved_paths
#print axioms forward_edgeOwner_of_decl_paths
#print axioms regionC8b_selectedForwardChild_stored_of_bucketTrace
#print axioms regionC8b_selectedForwardChild_emitted_of_bucketTrace

end Elegant.Layered.PipelineImpl
