import Elegant.GridArchitectureAnchorFacts
import Elegant.Kinds.Architecture
import Elegant.GridArchitectureRouteFacts
import Elegant.GridArchitectureGlobalCount

set_option autoImplicit false

namespace Elegant.Grid.Architecture.CellContracts

def initial (input : Input) (fuel : Nat) : Placement :=
  ⟨List.replicate (virtualParents input).length default,
    List.replicate input.groups.length default,
    List.replicate input.groups.length default, fuel, false⟩

def afterPrefix (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (before : List Nat) : Placement :=
  before.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
    (initial input fuel)

theorem group_execution_contract (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before ++ g :: suffix) :
    let state := afterPrefix input p fp fuel before
    let source := levelOf input p state.relative (Int.ofNat g)
    let result := (arrange p state.fuel source).1
    CellsUnique result ∧
      ∀ i, i < source.units.length → result.placed.getD i false = true := by
  intro state source result
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  rw [position] at full
  have executed := hierarchyRunEvidence_after_prefix input p fp before (g :: suffix)
    (initial input fuel) full
  exact ⟨executed.1.2.2.2, executed.2.2.1⟩

theorem root_execution_contract (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    let state := afterPrefix input p fp fuel (List.range input.groups.length).reverse
    let source := levelOf input p state.relative (-1)
    let result := (arrange p state.fuel source).1
    CellsUnique result ∧
      ∀ i, i < source.units.length → result.placed.getD i false = true := by
  intro state source result
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  have executed := hierarchyRunEvidence_after_prefix input p fp
    (List.range input.groups.length).reverse [] (initial input fuel)
    (by
      rw [List.append_nil]
      exact full)
  exact ⟨executed.1.2.2.2, executed.2.2⟩

theorem group_global_cells_unique (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before ++ g :: suffix) :
    let state := afterPrefix input p fp fuel before
    let result := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    ((result.units.zipIdx.filter (fun q => q.1.group < 0)).map
      (fun q => (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD
        q.1.node.toNat default)).Nodup :=
  executed_group_nodes_nodup input p fp fuel ordered px py padding line
    before suffix g position

theorem root_global_cells_unique (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    let state := afterPrefix input p fp fuel (List.range input.groups.length).reverse
    let result := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    ((result.units.zipIdx.filter (fun q => q.1.group < 0)).map
      (fun q => (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD
        q.1.node.toNat default)).Nodup :=
  executed_root_nodes_nodup input p fp fuel ordered px py padding line

theorem node_in_own_level (input : Input) (p : Params) (relative : List Span)
    (n : Nat) (bound : n < (virtualParents input).length) :
    (⟨Int.ofNat n, -1⟩ : Unit) ∈
      (levelOf input p relative ((virtualParents input).getD n (-1))).units := by
  change (⟨Int.ofNat n, -1⟩ : Unit) ∈ ((_ ++ _) : List Unit).mergeSort _
  rw [List.mem_mergeSort]
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨((virtualParents input).getD n (-1), n), ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_zipIdx_iff_getElem?.mpr ?_, by simp⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
    Option.getD_some]

theorem virtual_parent_admitted (input : Input)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (n : Nat) (bound : n < (virtualParents input).length) :
    (virtualParents input).getD n (-1) = -1 ∨
      ∃ g, g < input.groups.length ∧
        (virtualParents input).getD n (-1) = Int.ofNat g := by
  have member : (virtualParents input).getD n (-1) ∈ virtualParents input := by
    apply List.mem_of_getElem? (i := n)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
      Option.getD_some]
  rw [virtualParents] at member
  rcases List.mem_append.mp member with source | placeholder
  · exact parents _ source
  · obtain ⟨g, present, equal⟩ := List.mem_map.mp placeholder
    exact Or.inr ⟨g, List.mem_range.mp (List.mem_filter.mp present).1, equal.symm⟩

private theorem split_member (indices : List Nat) (g : Nat) (member : g ∈ indices) :
    ∃ before suffix, indices = before ++ g :: suffix := by
  induction indices with
  | nil => simp at member
  | cons a rest ih =>
    rcases List.mem_cons.mp member with same | present
    · subst a
      exact ⟨[], rest, rfl⟩
    · obtain ⟨before, suffix, equal⟩ := ih present
      exact ⟨a :: before, suffix, by simp only [equal, List.cons_append]⟩
theorem prefix_node_storage_length (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (before : List Nat) :
    (afterPrefix input p fp fuel before).localNodes.length =
      (virtualParents input).length := by
  have fold : ∀ (indices : List Nat) (state : Placement),
      (indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
        state).localNodes.length = state.localNodes.length := by
    intro indices
    induction indices with
    | nil => intro state; rfl
    | cons g rest ih =>
      intro state
      rw [List.foldl_cons, ih]
      exact (arrangeParent_storage_lengths input p fp (Int.ofNat g) state).1
  exact (fold before (initial input fuel)).trans (List.length_replicate ..)


def NodeExecuted (input : Input) (p : Params) (fp : FrameParams)
    (fuel n : Nat) : Prop :=
  ∃ parent before,
    (parent = -1 ∧ before = (List.range input.groups.length).reverse ∨
      ∃ g suffix, parent = Int.ofNat g ∧
        (List.range input.groups.length).reverse = before ++ g :: suffix) ∧
    (virtualParents input).getD n (-1) = parent ∧
    let state := afterPrefix input p fp fuel before
    let source := levelOf input p state.relative parent
    let result := (arrange p state.fuel source).1
    ∃ i, i < source.units.length ∧
      source.units[i]? = some (⟨Int.ofNat n, -1⟩ : Unit) ∧
      result.placed.getD i false = true ∧
      (placeHierarchy input p fp fuel).localNodes.getD n default =
        result.cells.getD i default

theorem source_node_execution_coverage (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g) :
    ∀ n, n < (virtualParents input).length → NodeExecuted input p fp fuel n := by
  intro n bound
  rcases virtual_parent_admitted input parents n bound with root | grouped
  · let before := (List.range input.groups.length).reverse
    let state := afterPrefix input p fp fuel before
    let source := levelOf input p state.relative (-1)
    have member : (⟨Int.ofNat n, -1⟩ : Unit) ∈ source.units := by
      simpa only [root] using node_in_own_level input p state.relative n bound
    obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
    have ibound := (List.getElem?_eq_some_iff.mp lookup).choose
    refine ⟨-1, before, Or.inl ⟨rfl, rfl⟩, root, i, ibound, lookup, ?_, ?_⟩
    · exact arranged_parent_all_placed input p state.relative (-1) state.fuel i ibound
    · have storage := prefix_node_storage_length input p fp fuel before
      have indexed : (⟨Int.ofNat n, -1⟩, i) ∈
          (arrange p state.fuel source).1.units.zipIdx := by
        apply List.mem_zipIdx_iff_getElem?.mpr
        simpa only [arrange_units] using lookup
      have stored := (arrangeParent_node_placement input p fp (-1) state storage
        (⟨Int.ofNat n, -1⟩, i) indexed (by change (-1 : Int) < 0; omega)).1
      change (arrangeParent input p fp (-1) state).localNodes.getD n default = _
      simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast] using stored
  · obtain ⟨g, gbound, owner⟩ := grouped
    obtain ⟨before, suffix, position⟩ :=
      split_member (List.range input.groups.length).reverse g
        (List.mem_reverse.mpr (List.mem_range.mpr gbound))
    let state := afterPrefix input p fp fuel before
    let source := levelOf input p state.relative (Int.ofNat g)
    have member : (⟨Int.ofNat n, -1⟩ : Unit) ∈ source.units := by
      simpa only [owner] using node_in_own_level input p state.relative n bound
    obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
    have ibound := (List.getElem?_eq_some_iff.mp lookup).choose
    refine ⟨Int.ofNat g, before, Or.inr ⟨g, suffix, rfl, position⟩,
      owner, i, ibound, lookup, ?_, ?_⟩
    · exact arranged_parent_all_placed input p state.relative (Int.ofNat g)
        state.fuel i ibound
    · have decreasing :
          ((List.range input.groups.length).reverse).Pairwise (fun a b => b < a) :=
        List.pairwise_reverse.mpr List.pairwise_lt_range
      rw [position] at decreasing
      have lower : ∀ k ∈ suffix, k < g :=
        (List.pairwise_cons.mp (List.pairwise_append.mp decreasing).2.1).1
      have storage := prefix_node_storage_length input p fp fuel before
      have indexed : (⟨Int.ofNat n, -1⟩, i) ∈
          (arrange p state.fuel source).1.units.zipIdx := by
        apply List.mem_zipIdx_iff_getElem?.mpr
        simpa only [arrange_units] using lookup
      have stored := group_node_placement_survives_suffix input p fp g suffix
        lower state storage (⟨Int.ofNat n, -1⟩, i) indexed
        (by change (-1 : Int) < 0; omega)
      change (arrangeParent input p fp (-1)
        (((List.range input.groups.length).reverse).foldl
          (fun state k => arrangeParent input p fp (Int.ofNat k) state)
          (initial input fuel))).localNodes.getD n default = _
      rw [position, List.foldl_append, List.foldl_cons]
      simpa only [state, source, afterPrefix, Int.ofNat_eq_natCast,
        Int.toNat_natCast] using stored

private theorem decoded_node_parents {α : Type}
    (groups : List ModelBox) (source : List α) (nodes : List Node)
    (parentId : α → String) (make : α → Int → Node)
    (make_parent : ∀ a parent, (make a parent).parent = parent)
    (decoded : source.mapM (fun a =>
      (if (parentId a).isEmpty then
        (Except.ok (-1) : Except LayoutError Int)
      else match groups.findIdx? (fun (b : ModelBox) => b.id == parentId a) with
        | some i => .ok (Int.ofNat i)
        | none => .error .domain).bind (fun parent => pure (make a parent))) = .ok nodes) :
    ∀ parent ∈ nodes.map (·.parent),
      parent = -1 ∨ ∃ g, g < groups.length ∧ parent = Int.ofNat g := by
  have pairs : ∀ (xs : List α) (ys : List Node),
      xs.mapM (fun a =>
        (if (parentId a).isEmpty then
          (Except.ok (-1) : Except LayoutError Int)
        else match groups.findIdx? (fun (b : ModelBox) => b.id == parentId a) with
          | some i => .ok (Int.ofNat i)
          | none => .error .domain).bind (fun parent => pure (make a parent))) = .ok ys →
      ∀ b ∈ ys, b.parent = -1 ∨
        ∃ g, g < groups.length ∧ b.parent = Int.ofNat g := by
    intro xs
    induction xs with
    | nil =>
      intro ys h
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst ys
      simp
    | cons a rest ih =>
      intro ys h
      let decode : α → Except LayoutError Node := fun a =>
        (if (parentId a).isEmpty then
          (Except.ok (-1) : Except LayoutError Int)
        else match groups.findIdx? (fun (b : ModelBox) => b.id == parentId a) with
          | some i => .ok (Int.ofNat i)
          | none => .error .domain).bind (fun parent => pure (make a parent))
      rw [List.mapM_cons] at h
      change (do let b ← decode a; List.cons b <$> rest.mapM decode) =
        Except.ok ys at h
      cases empty : (parentId a).isEmpty with
      | true =>
        have head : decode a = .ok (make a (-1)) := by
          simp only [decode, empty, ite_true, pure, Except.pure, Except.bind]
        rw [head] at h
        cases tail : rest.mapM decode with
        | error e =>
          rw [tail] at h
          cases h
        | ok bs =>
          rw [tail] at h
          have same : make a (-1) :: bs = ys := Except.ok.inj h
          subst ys
          intro b member
          rcases List.mem_cons.mp member with same | later
          · subst b
            exact Or.inl (make_parent a (-1))
          · exact ih bs tail b later
      | false =>
        cases found : groups.findIdx? (fun b => b.id == parentId a) with
        | none =>
          have head : decode a = .error .domain := by
            simp only [decode, empty, Bool.false_eq_true, ite_false, found,
              Except.bind]
          rw [head] at h
          cases h
        | some g =>
          have head : decode a = .ok (make a (Int.ofNat g)) := by
            simp only [decode, empty, Bool.false_eq_true, ite_false, found,
              pure, Except.pure, Except.bind]
          rw [head] at h
          cases tail : rest.mapM decode with
          | error e =>
            rw [tail] at h
            cases h
          | ok bs =>
            rw [tail] at h
            have same : make a (Int.ofNat g) :: bs = ys := Except.ok.inj h
            subst ys
            intro b member
            rcases List.mem_cons.mp member with same | later
            · subst b
              exact Or.inr ⟨g,
                (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1,
                make_parent a (Int.ofNat g)⟩
            · exact ih bs tail b later
  intro parent member
  obtain ⟨node, present, rfl⟩ := List.mem_map.mp member
  exact pairs source nodes decoded node present

theorem public_build_execution_coverage (m : Model) (scene : Scene) (capped : Bool)
    (success : Kinds.Architecture.build m = .ok (scene, capped)) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      capped = (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat).budgetExhausted ∧
      ∀ n, n < (virtualParents input).length →
        NodeExecuted input p fp
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat n := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, gp, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Kinds.Architecture.build_success m scene capped success
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hsize,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hitems, hscene, hcapped⟩
  have groupLength : groupInput.length = groups.length := by
    have lengths : ∀ {α β : Type} (xs : List α) (f : α → Except LayoutError β)
        (ys : List β), xs.mapM f = .ok ys → xs.length = ys.length := by
      intro α β xs
      induction xs with
      | nil =>
        intro f ys h
        have same : [] = ys := by
          simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using h
        subst ys
        rfl
      | cons a rest ih =>
        intro f ys h
        cases first : f a with
        | error e =>
          simp [List.mapM_cons, first, bind, Except.bind] at h
        | ok b =>
          cases tail : rest.mapM f with
          | error e =>
            simp [List.mapM_cons, first, tail, bind, Except.bind] at h
          | ok bs =>
            have same : b :: bs = ys := by
              simpa [List.mapM_cons, first, tail, bind, Except.bind,
                Functor.map, Except.map, pure, Except.pure] using h
            subst ys
            simp only [List.length_cons, ih f bs tail]
    have gt := lengths groups _ titles htitles
    have gi := lengths (groups.zip titles) _ groupInput hgroupInput
    rw [List.length_zip, ← gt, Nat.min_self] at gi
    exact gi.symm
  have parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
    rw [hinput]
    change ∀ parent ∈ nodeInput.map (·.parent),
      parent = -1 ∨ ∃ g, g < groupInput.length ∧ parent = Int.ofNat g
    rw [groupLength]
    refine decoded_node_parents groups (nodes.zip captions) nodeInput
      (fun q => q.1.parent)
      (fun q parent =>
        let junction := (q.1.shape.splitOn ";").head! == "junction"
        let size := if junction then LayoutConst.architecture_junction_size.get profile else iw
        let height := if junction then size else ih
        { parent := parent, junction := junction, icon := { w := size, h := height },
          label := ⟨min COORD_LIMIT (Kinds.Common.widest q.2),
            min COORD_LIMIT ((q.2.length : Int) * lh)⟩ })
      (by intros; rfl) hnodeInput
  refine ⟨input, params, frameParams, ?_, ?_⟩
  · simp only [hplaced, hprofile]
  · simpa only [hprofile] using source_node_execution_coverage input params
      frameParams (LayoutConst.architecture_bfs_cap.get profile).toNat parents

theorem arch_all_placed (m : Model) (result : Layered.FamilyResult)
    (success : Kinds.Architecture.layout m = .ok result) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      result.budgetExhausted = (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat).budgetExhausted ∧
      ∀ n, n < (virtualParents input).length →
        NodeExecuted input p fp
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat n := by
  unfold Kinds.Architecture.layout at success
  by_cases nodes : m.boxes.length > m.options.limits.maxNodes
  · simp [nodes, bind, Except.bind, throw] at success
  · simp only [nodes, ↓reduceIte, bind, Except.bind, pure, Except.pure] at success
    by_cases edges : m.routes.length > m.options.limits.maxEdges
    · simp [edges, throw] at success
    · simp only [edges, ↓reduceIte] at success
      split at success
      · simp [throw] at success
      ·
        cases built : Kinds.Architecture.build m with
        | error error => simp [built, throw] at success
        | ok pair =>
          obtain ⟨scene, capped⟩ := pair
          have equal : result = {
              scene := scene.projectCellAttachments (Kinds.Common.routeMarkers m)
              budgetExhausted := capped } := by
            simpa only [built, pure, Except.pure, Except.ok.injEq] using success.symm
          subst result
          exact public_build_execution_coverage m scene capped built

theorem same_parent_global_cells_distinct (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (a b : Nat) (ha : a < (virtualParents input).length)
    (hb : b < (virtualParents input).length) (different : a ≠ b)
    (sameParent : (virtualParents input).getD a (-1) =
      (virtualParents input).getD b (-1)) :
    (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD a default ≠
      (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD b default := by
  obtain ⟨parent, before, executed, owner, rest⟩ :=
    source_node_execution_coverage input p fp fuel parents a ha
  let state := afterPrefix input p fp fuel before
  let source := levelOf input p state.relative parent
  have leftMember : (⟨Int.ofNat a, -1⟩ : Unit) ∈ source.units := by
    simpa only [owner] using node_in_own_level input p state.relative a ha
  have rightOwner : (virtualParents input).getD b (-1) = parent :=
    sameParent.symm.trans owner
  have rightMember : (⟨Int.ofNat b, -1⟩ : Unit) ∈ source.units := by
    simpa only [rightOwner] using node_in_own_level input p state.relative b hb
  obtain ⟨i, leftLookup⟩ := List.mem_iff_getElem?.mp leftMember
  obtain ⟨j, rightLookup⟩ := List.mem_iff_getElem?.mp rightMember
  have indices : i ≠ j := by
    intro equal
    rw [equal, rightLookup] at leftLookup
    have units := Option.some.inj leftLookup
    have nodes := congrArg Unit.node units
    apply different
    exact Int.ofNat.inj nodes.symm
  have leftIndexed : ((⟨Int.ofNat a, -1⟩ : Unit), i) ∈
      (arrange p state.fuel source).1.units.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [arrange_units] using leftLookup
  have rightIndexed : ((⟨Int.ofNat b, -1⟩ : Unit), j) ∈
      (arrange p state.fuel source).1.units.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [arrange_units] using rightLookup
  rcases executed with root | grouped
  · rcases root with ⟨rfl, rfl⟩
    simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast] using
      executed_root_nodes_distinct input p fp fuel ordered px py padding line
        _ leftIndexed _ rightIndexed
          (by change (-1 : Int) < 0; omega)
          (by change (-1 : Int) < 0; omega) indices
  · obtain ⟨g, suffix, rfl, position⟩ := grouped
    simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast] using
      executed_group_nodes_distinct input p fp fuel ordered px py padding line
        before suffix g position _ leftIndexed _ rightIndexed
          (by change (-1 : Int) < 0; omega)
          (by change (-1 : Int) < 0; omega) indices

theorem group_relative_contains_node_tile (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (n g : Nat) (hn : n < (virtualParents input).length)
    (hg : g < input.groups.length)
    (owner : (virtualParents input).getD n (-1) = Int.ofNat g) :
    let placed := placeHierarchy input p fp fuel
    (placed.relative.getD g default).contains
      ((⟨0, 0, p.pitchX, p.pitchY⟩ : Span).shift
        ((placed.localNodes.getD n default).x * p.pitchX)
        ((placed.localNodes.getD n default).y * p.pitchY)) := by
  obtain ⟨before, suffix, position⟩ :=
    split_member (List.range input.groups.length).reverse g
      (List.mem_reverse.mpr (List.mem_range.mpr hg))
  let state := afterPrefix input p fp fuel before
  let source := levelOf input p state.relative (Int.ofNat g)
  let result := (arrange p state.fuel source).1
  have member : (⟨Int.ofNat n, -1⟩ : Unit) ∈ source.units := by
    simpa only [owner] using node_in_own_level input p state.relative n hn
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
  have ibound := (List.getElem?_eq_some_iff.mp lookup).choose
  have indexed : ((⟨Int.ofNat n, -1⟩ : Unit), i) ∈ result.units.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [result, arrange_units] using lookup
  have full := placeHierarchy_execution_invariants input p fp fuel
    ordered px py padding line
  rw [position] at full
  have executed := hierarchyRunEvidence_after_prefix input p fp before (g :: suffix)
    (initial input fuel) full
  have coordinates := executed.1.2.1.2.2 i
    (by rw [arrange_placed_length, level_placed_length]; exact ibound)
    (arranged_parent_all_placed input p state.relative (Int.ofNat g) state.fuel i ibound)
  change result.absolute.getD i default =
    (result.rects.getD i default).shift
      ((result.cells.getD i default).x * p.pitchX)
      ((result.cells.getD i default).y * p.pitchY) at coordinates
  have rectLookup : source.rects[i]? =
      some (⟨0, 0, p.pitchX, p.pitchY⟩ : Span) := by
    change (source.units.map (fun u => if u.group < 0 then
      (⟨0, 0, p.pitchX, p.pitchY⟩ : Span)
      else state.relative.getD u.group.toNat default))[i]? = _
    rw [List.getElem?_map, lookup]
    rfl
  have rectAt : result.rects.getD i default = (⟨0, 0, p.pitchX, p.pitchY⟩ : Span) := by
    rw [arrange_rects]
    simp only [List.getD_eq_getElem?_getD, rectLookup, Option.getD_some]
  have decreasing :
      ((List.range input.groups.length).reverse).Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr List.pairwise_lt_range
  rw [position] at decreasing
  have lower : ∀ k ∈ suffix, k < g :=
    (List.pairwise_cons.mp (List.pairwise_append.mp decreasing).2.1).1
  have stored := group_node_placement_survives_suffix input p fp g suffix lower state
    (prefix_node_storage_length input p fp fuel before)
    ((⟨Int.ofNat n, -1⟩ : Unit), i) indexed
    (by change (-1 : Int) < 0; omega)
  have finalStored : (placeHierarchy input p fp fuel).localNodes.getD n default =
      result.cells.getD i default := by
    change (arrangeParent input p fp (-1)
      (((List.range input.groups.length).reverse).foldl
        (fun state k => arrangeParent input p fp (Int.ofNat k) state)
        (initial input fuel))).localNodes.getD n default = _
    rw [position, List.foldl_append, List.foldl_cons]
    simpa only [result, source, state, afterPrefix, initial, Int.ofNat_eq_natCast,
      Int.toNat_natCast] using stored
  have inside := executed_group_frame_contains_unit input p fp fuel
    ordered px py padding line before suffix g position i
    (by
      change i < result.units.length
      simpa only [result, arrange_units] using ibound)
  change ((placeHierarchy input p fp fuel).relative.getD g default).contains
    (result.absolute.getD i default) at inside
  dsimp only
  rw [finalStored]
  rw [coordinates, rectAt] at inside
  exact inside

theorem hierarchy_relative_length (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat) :
    (placeHierarchy input p fp fuel).relative.length = input.groups.length := by
  have fold : ∀ (indices : List Nat) (state : Placement),
      (indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
        state).relative.length = state.relative.length := by
    intro indices
    induction indices with
    | nil => intro state; rfl
    | cons g rest ih =>
      intro state
      rw [List.foldl_cons, ih]
      exact arrangeParent_relative_length input p fp (Int.ofNat g) state
  change (arrangeParent input p fp (-1)
    (((List.range input.groups.length).reverse).foldl
      (fun state g => arrangeParent input p fp (Int.ofNat g) state)
      (initial input fuel))).relative.length = _
  rw [arrangeParent_relative_length, fold]
  exact List.length_replicate ..

private theorem indexed_map_at {α β : Type} (items : List α)
    (f : α × Nat → β) (i : Nat) (a : α) (b : β) (bound : i < items.length) :
    (items.zipIdx.map f).getD i b = f (items.getD i a, i) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem bound, Option.map_some, Option.getD_some, Nat.zero_add]

theorem resolved_group_contains_node_tile (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (n g : Nat) (hn : n < (virtualParents input).length)
    (hg : g < input.groups.length)
    (owner : (virtualParents input).getD n (-1) = Int.ofNat g) :
    let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
    (resolved.frames.getD g default).contains
      ((⟨0, 0, p.pitchX, p.pitchY⟩ : Span).shift
        ((resolved.nodes.getD n default).x * p.pitchX)
        ((resolved.nodes.getD n default).y * p.pitchY)) := by
  let placed := placeHierarchy input p fp fuel
  obtain ⟨origins, originLength, originEquations, frames, nodes⟩ :=
    resolveHierarchy_execution input p placed ordered
  have relativeLength : placed.relative.length = input.groups.length :=
    hierarchy_relative_length input p fp fuel
  have frameAt : (resolveHierarchy input p placed).frames.getD g default =
      (placed.relative.getD g default).shift
        ((origins.getD g default).x * p.pitchX)
        ((origins.getD g default).y * p.pitchY) := by
    rw [frames, indexed_map_at _ _ g default default (by omega)]
  have nodeAt : (resolveHierarchy input p placed).nodes.getD n default =
      (⟨(origins.getD g default).x + (placed.localNodes.getD n default).x,
        (origins.getD g default).y + (placed.localNodes.getD n default).y⟩ : Cell) := by
    rw [nodes, indexed_map_at _ _ n (-1) default hn, owner]
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast,
      show ¬(g : Int) < 0 by omega, ↓reduceIte]
  have localInside := group_relative_contains_node_tile input p fp fuel
    ordered px py padding line n g hn hg owner
  change ((resolveHierarchy input p placed).frames.getD g default).contains
    ((⟨0, 0, p.pitchX, p.pitchY⟩ : Span).shift
      (((resolveHierarchy input p placed).nodes.getD n default).x * p.pitchX)
      (((resolveHierarchy input p placed).nodes.getD n default).y * p.pitchY))
  rw [frameAt, nodeAt]
  change (placed.relative.getD g default).contains
    ((⟨0, 0, p.pitchX, p.pitchY⟩ : Span).shift
      ((placed.localNodes.getD n default).x * p.pitchX)
      ((placed.localNodes.getD n default).y * p.pitchY)) at localInside
  simp only [Span.contains, Span.shift, Int.add_mul] at localInside ⊢
  omega

theorem level_group_owner (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (u : Unit)
    (member : u ∈ (levelOf input p relative parent).units)
    (group : 0 ≤ u.group) :
    u.group.toNat < input.groups.length ∧
      (input.groups.getD u.group.toNat default).parent = parent := by
  change u ∈ ((_ ++ _) : List Unit).mergeSort _ at member
  rw [List.mem_mergeSort] at member
  rcases List.mem_append.mp member with nodes | groups
  · obtain ⟨q, _, equal⟩ := List.mem_map.mp nodes
    subst u
    dsimp only at group
    omega
  · obtain ⟨q, present, rfl⟩ := List.mem_map.mp groups
    obtain ⟨indexed, owns⟩ := List.mem_filter.mp present
    have lookup := List.mem_zipIdx_iff_getElem?.mp indexed
    have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    have actual : input.groups.getD q.2 default = q.1 := by
      simp only [List.getD_eq_getElem?_getD, lookup, Option.getD_some]
    simp only [Int.toNat_natCast]
    exact ⟨bound, by simpa only [actual, beq_iff_eq] using owns⟩

def GroupKeysDistinct (units : List Unit) : Prop :=
  units.Pairwise (fun a b => 0 ≤ a.group → 0 ≤ b.group →
    a.group.toNat ≠ b.group.toNat)

theorem level_group_keys_distinct (input : Input) (p : Params)
    (relative : List Span) (parent : Int) :
    GroupKeysDistinct (levelOf input p relative parent).units := by
  let nodes := ((virtualParents input).zipIdx.filter (fun q => q.1 == parent)).map
    (fun q => (⟨q.2, -1⟩ : Unit))
  let groups := (input.groups.zipIdx.filter (fun q => q.1.parent == parent)).map
    (fun q => (⟨-1, q.2⟩ : Unit))
  have nodeKeys : GroupKeysDistinct nodes := by
    apply List.pairwise_map.mpr
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj less group _
    dsimp only at group
    omega
  have groupKeys : GroupKeysDistinct groups := by
    have numbered : (input.groups.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    have pairs := List.pairwise_map.mp numbered
    have filtered := List.Pairwise.filter
      (fun q : Group × Nat => q.1.parent == parent) pairs
    apply List.pairwise_map.mpr
    exact filtered.imp (by
      intro a b different _ _
      simpa only [Int.toNat_natCast] using different)
  have combined : GroupKeysDistinct (nodes ++ groups) := by
    apply List.pairwise_append.mpr
    refine ⟨nodeKeys, groupKeys, ?_⟩
    intro a member b _ group _
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp member
    dsimp only at group
    omega
  have symmetric : ∀ {a b : Unit},
      (0 ≤ a.group → 0 ≤ b.group → a.group.toNat ≠ b.group.toNat) →
      0 ≤ b.group → 0 ≤ a.group → b.group.toNat ≠ a.group.toNat := by
    intro a b different hb ha
    exact Ne.symm (different ha hb)
  exact ((List.mergeSort_perm (nodes ++ groups) _).symm.pairwise_iff symmetric).mp combined

private theorem group_writes_preserve_foreign (l : Level)
    (entries : List (Unit × Nat)) (state : Placement) (target : Nat)
    (foreign : ∀ q ∈ entries, 0 ≤ q.1.group → q.1.group.toNat ≠ target) :
    (entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
      else { state with localGroups := state.localGroups.set q.1.group.toNat c })
      state).localGroups.getD target default = state.localGroups.getD target default := by
  induction entries generalizing state with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by intro entry present; exact foreign entry (by simp [present]))]
    split
    · rfl
    · rename_i group
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (foreign q (by simp) (by omega))]

private theorem group_writes_lookup (l : Level) (entries : List (Unit × Nat))
    (state : Placement) (q : Unit × Nat) (member : q ∈ entries)
    (group : 0 ≤ q.1.group) (bound : q.1.group.toNat < state.localGroups.length)
    (keys : GroupKeysDistinct (entries.map Prod.fst)) :
    (entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
      else { state with localGroups := state.localGroups.set q.1.group.toNat c })
      state).localGroups.getD q.1.group.toNat default = l.cells.getD q.2 default := by
  induction entries generalizing state with
  | nil => simp only [List.not_mem_nil] at member
  | cons first rest ih =>
    have pairwise := List.pairwise_map.mp keys
    have headKeys := (List.pairwise_cons.mp pairwise).1
    have tailKeys : GroupKeysDistinct (rest.map Prod.fst) :=
      List.pairwise_map.mpr (List.pairwise_cons.mp pairwise).2
    rcases List.mem_cons.mp member with same | tail
    · subst q
      simp only [List.foldl_cons, show ¬first.1.group < 0 by omega, ↓reduceIte]
      have foreign : ∀ entry ∈ rest, 0 ≤ entry.1.group →
          entry.1.group.toNat ≠ first.1.group.toNat := by
        intro entry present isGroup
        exact Ne.symm (headKeys entry present group isGroup)
      rw [group_writes_preserve_foreign l rest _ _ foreign]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self bound, Option.getD_some]
    · simp only [List.foldl_cons]
      apply ih _ tail _ tailKeys
      split <;> simpa only [List.length_set] using bound

theorem arrangeParent_group_placement (input : Input) (p : Params)
    (fp : FrameParams) (parent : Int) (state : Placement)
    (storage : state.localGroups.length = input.groups.length)
    (q : Unit × Nat)
    (member : q ∈ (arrange p state.fuel
      (levelOf input p state.relative parent)).1.units.zipIdx)
    (group : 0 ≤ q.1.group) :
    (arrangeParent input p fp parent state).localGroups.getD q.1.group.toNat default =
      (arrange p state.fuel (levelOf input p state.relative parent)).1.cells.getD q.2 default := by
  let l := (arrange p state.fuel (levelOf input p state.relative parent)).1
  have original : q.1 ∈ (levelOf input p state.relative parent).units := by
    have present : q.1 ∈ l.units :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
    simpa only [l, arrange_units] using present
  have owner := level_group_owner input p state.relative parent q.1 original group
  have keys : GroupKeysDistinct (l.units.zipIdx.map Prod.fst) := by
    rw [List.zipIdx_map_fst]
    simpa only [l, arrange_units] using
      level_group_keys_distinct input p state.relative parent
  let seeded : Placement := ⟨state.localNodes, state.localGroups, state.relative,
    (arrange p state.fuel (levelOf input p state.relative parent)).2,
    state.budgetExhausted || l.budgetExhausted⟩
  have stored := group_writes_lookup l l.units.zipIdx seeded
    q member group
      (by change q.1.group.toNat < state.localGroups.length; rw [storage]; exact owner.1)
      keys
  unfold arrangeParent
  split <;> exact stored

theorem arrangeParent_preserves_foreign_group (input : Input) (p : Params)
    (fp : FrameParams) (parent : Int) (state : Placement) (target : Nat)
    (foreign : (input.groups.getD target default).parent ≠ parent) :
    (arrangeParent input p fp parent state).localGroups.getD target default =
      state.localGroups.getD target default := by
  let l := (arrange p state.fuel (levelOf input p state.relative parent)).1
  let seeded : Placement := ⟨state.localNodes, state.localGroups, state.relative,
    (arrange p state.fuel (levelOf input p state.relative parent)).2,
    state.budgetExhausted || l.budgetExhausted⟩
  have preserved := group_writes_preserve_foreign l l.units.zipIdx seeded target
    (by
      intro q member group same
      have unitMember : q.1 ∈ l.units :=
        List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
      have original : q.1 ∈ (levelOf input p state.relative parent).units := by
        simpa only [l, arrange_units] using unitMember
      have owner := (level_group_owner input p state.relative parent q.1 original group).2
      rw [same] at owner
      exact foreign owner)
  unfold arrangeParent
  split <;> exact preserved

theorem hierarchy_fold_preserves_foreign_group (input : Input) (p : Params)
    (fp : FrameParams) (indices : List Nat) (state : Placement) (target : Nat)
    (foreign : ∀ g ∈ indices,
      (input.groups.getD target default).parent ≠ Int.ofNat g) :
    (indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
      state).localGroups.getD target default = state.localGroups.getD target default := by
  induction indices generalizing state with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih _ (by intro i member; exact foreign i (by simp [member]))]
    exact arrangeParent_preserves_foreign_group input p fp (Int.ofNat g) state target
      (foreign g (by simp))

theorem hierarchy_fold_preserves_other_frame (input : Input) (p : Params)
    (fp : FrameParams) (indices : List Nat) (state : Placement) (target : Nat)
    (foreign : ∀ g ∈ indices, g ≠ target) :
    (indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
      state).relative.getD target default = state.relative.getD target default := by
  induction indices generalizing state with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih _ (by intro i member; exact foreign i (by simp [member]))]
    exact arrangeParent_preserves_other_frame input p fp g target state
      (foreign g (by simp))

theorem child_group_placement_survives_suffix (input : Input) (p : Params)
    (fp : FrameParams) (g child : Nat) (suffix : List Nat) (state : Placement)
    (lower : ∀ k ∈ suffix, k < g) (afterParent : g < child)
    (owner : (input.groups.getD child default).parent = Int.ofNat g)
    (storage : state.localGroups.length = input.groups.length)
    (i : Nat)
    (member : ((⟨-1, Int.ofNat child⟩ : Unit), i) ∈
      (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1.units.zipIdx) :
    let final := arrangeParent input p fp (-1)
      (suffix.foldl (fun state k => arrangeParent input p fp (Int.ofNat k) state)
        (arrangeParent input p fp (Int.ofNat g) state))
    final.localGroups.getD child default =
        (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1.cells.getD i default ∧
      final.relative.getD child default = state.relative.getD child default := by
  constructor
  · rw [arrangeParent_preserves_foreign_group input p fp (-1) _ child
      (by rw [owner]; simp only [Int.ofNat_eq_natCast]; omega)]
    rw [hierarchy_fold_preserves_foreign_group input p fp suffix _ child (by
      intro k present
      have bound := lower k present
      rw [owner]
      simp only [Int.ofNat_eq_natCast]
      omega)]
    simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast] using
      arrangeParent_group_placement input p fp (Int.ofNat g) state storage
        ((⟨-1, Int.ofNat child⟩ : Unit), i) member
        (by change (0 : Int) ≤ Int.ofNat child; exact Int.natCast_nonneg child)
  · rw [arrangeParent_relative]
    simp only [show (-1 : Int) < 0 by decide, ↓reduceIte]
    rw [hierarchy_fold_preserves_other_frame input p fp suffix _ child (by
      intro k present
      have bound := lower k present
      omega)]
    exact arrangeParent_preserves_other_frame input p fp g child state (by omega)

theorem group_in_own_level (input : Input) (p : Params) (relative : List Span)
    (child : Nat) (bound : child < input.groups.length) :
    (⟨-1, Int.ofNat child⟩ : Unit) ∈
      (levelOf input p relative (input.groups.getD child default).parent).units := by
  change (⟨-1, Int.ofNat child⟩ : Unit) ∈ ((_ ++ _) : List Unit).mergeSort _
  rw [List.mem_mergeSort]
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(input.groups.getD child default, child), ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_zipIdx_iff_getElem?.mpr ?_, by simp⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound,
    Option.getD_some]

theorem group_relative_contains_child_frame (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (child g : Nat) (hc : child < input.groups.length)
    (hg : g < input.groups.length)
    (owner : (input.groups.getD child default).parent = Int.ofNat g) :
    let placed := placeHierarchy input p fp fuel
    (placed.relative.getD g default).contains
      ((placed.relative.getD child default).shift
        ((placed.localGroups.getD child default).x * p.pitchX)
        ((placed.localGroups.getD child default).y * p.pitchY)) := by
  have afterParent : g < child := by
    have order := ordered child hc
    rw [owner] at order
    simp only [Int.ofNat_eq_natCast] at order
    omega
  obtain ⟨before, suffix, position⟩ :=
    split_member (List.range input.groups.length).reverse g
      (List.mem_reverse.mpr (List.mem_range.mpr hg))
  let state := afterPrefix input p fp fuel before
  let source := levelOf input p state.relative (Int.ofNat g)
  let result := (arrange p state.fuel source).1
  have member : (⟨-1, Int.ofNat child⟩ : Unit) ∈ source.units := by
    simpa only [owner] using group_in_own_level input p state.relative child hc
  obtain ⟨i, lookup⟩ := List.mem_iff_getElem?.mp member
  have ibound := (List.getElem?_eq_some_iff.mp lookup).choose
  have indexed : ((⟨-1, Int.ofNat child⟩ : Unit), i) ∈ result.units.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [result, arrange_units] using lookup
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  rw [position] at full
  have executed := hierarchyRunEvidence_after_prefix input p fp before (g :: suffix)
    (initial input fuel) full
  have coordinates := executed.1.2.1.2.2 i
    (by rw [arrange_placed_length, level_placed_length]; exact ibound)
    (arranged_parent_all_placed input p state.relative (Int.ofNat g) state.fuel i ibound)
  change result.absolute.getD i default =
    (result.rects.getD i default).shift
      ((result.cells.getD i default).x * p.pitchX)
      ((result.cells.getD i default).y * p.pitchY) at coordinates
  have rectLookup : source.rects[i]? = some (state.relative.getD child default) := by
    change (source.units.map (fun u => if u.group < 0 then
      (⟨0, 0, p.pitchX, p.pitchY⟩ : Span)
      else state.relative.getD u.group.toNat default))[i]? = _
    rw [List.getElem?_map, lookup]
    simp only [Option.map_some, Int.ofNat_eq_natCast, Int.toNat_natCast]
    rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg child))]
  have rectAt : result.rects.getD i default = state.relative.getD child default := by
    rw [arrange_rects]
    simp only [List.getD_eq_getElem?_getD, rectLookup, Option.getD_some]
  have decreasing :
      ((List.range input.groups.length).reverse).Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr List.pairwise_lt_range
  rw [position] at decreasing
  have lower : ∀ k ∈ suffix, k < g :=
    (List.pairwise_cons.mp (List.pairwise_append.mp decreasing).2.1).1
  have storage : state.localGroups.length = input.groups.length := by
    have fold : ∀ (indices : List Nat) (seed : Placement),
        (indices.foldl (fun seed k => arrangeParent input p fp (Int.ofNat k) seed)
          seed).localGroups.length = seed.localGroups.length := by
      intro indices
      induction indices with
      | nil => intro seed; rfl
      | cons k rest ih =>
        intro seed
        rw [List.foldl_cons, ih]
        exact (arrangeParent_storage_lengths input p fp (Int.ofNat k) seed).2.1
    exact (fold before (initial input fuel)).trans (List.length_replicate ..)
  have survives := child_group_placement_survives_suffix input p fp g child suffix state
    lower afterParent owner storage i indexed
  have hierarchy : placeHierarchy input p fp fuel =
      arrangeParent input p fp (-1)
        (suffix.foldl (fun state k => arrangeParent input p fp (Int.ofNat k) state)
          (arrangeParent input p fp (Int.ofNat g) state)) := by
    change arrangeParent input p fp (-1)
      (((List.range input.groups.length).reverse).foldl
        (fun state k => arrangeParent input p fp (Int.ofNat k) state)
        (initial input fuel)) = _
    rw [position, List.foldl_append, List.foldl_cons]
    rfl
  change (arrangeParent input p fp (-1)
    (suffix.foldl (fun state k => arrangeParent input p fp (Int.ofNat k) state)
      (arrangeParent input p fp (Int.ofNat g) state))).localGroups.getD child default =
      result.cells.getD i default ∧
    (arrangeParent input p fp (-1)
      (suffix.foldl (fun state k => arrangeParent input p fp (Int.ofNat k) state)
        (arrangeParent input p fp (Int.ofNat g) state))).relative.getD child default =
      state.relative.getD child default at survives
  rw [← hierarchy] at survives
  have inside := executed_group_frame_contains_unit input p fp fuel ordered px py
    padding line before suffix g position i (by
      change i < result.units.length
      simpa only [result, arrange_units] using ibound)
  change ((placeHierarchy input p fp fuel).relative.getD g default).contains
    (result.absolute.getD i default) at inside
  rw [coordinates, rectAt, ← survives.1, ← survives.2] at inside
  exact inside

theorem resolved_group_contains_child_frame (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (child g : Nat) (hc : child < input.groups.length)
    (hg : g < input.groups.length)
    (owner : (input.groups.getD child default).parent = Int.ofNat g) :
    let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
    (resolved.frames.getD g default).contains (resolved.frames.getD child default) := by
  let placed := placeHierarchy input p fp fuel
  obtain ⟨origins, originLength, originEquations, frames, nodes⟩ :=
    resolveHierarchy_execution input p placed ordered
  have relativeLength : placed.relative.length = input.groups.length :=
    hierarchy_relative_length input p fp fuel
  have frameAt : ∀ k, k < input.groups.length →
      (resolveHierarchy input p placed).frames.getD k default =
        (placed.relative.getD k default).shift
          ((origins.getD k default).x * p.pitchX)
          ((origins.getD k default).y * p.pitchY) := by
    intro k hk
    rw [frames, indexed_map_at _ _ k default default (by omega)]
  have childLookup : input.groups[child]? =
      some (input.groups.getD child default) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc,
      Option.getD_some]
  have originAt := originEquations (input.groups.getD child default, child)
    (List.mem_zipIdx_iff_getElem?.mpr childLookup)
  change origins.getD child default =
    (⟨(if (input.groups.getD child default).parent < 0 then
          (default : Cell) else
          origins.getD (input.groups.getD child default).parent.toNat default).x +
        (placed.localGroups.getD child default).x,
      (if (input.groups.getD child default).parent < 0 then
          (default : Cell) else
          origins.getD (input.groups.getD child default).parent.toNat default).y +
        (placed.localGroups.getD child default).y⟩ : Cell) at originAt
  rw [owner] at originAt
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast,
    show ¬(g : Int) < 0 by omega, ↓reduceIte] at originAt
  have localInside := group_relative_contains_child_frame input p fp fuel
    ordered px py padding line child g hc hg owner
  change ((resolveHierarchy input p placed).frames.getD g default).contains
    ((resolveHierarchy input p placed).frames.getD child default)
  rw [frameAt g hg, frameAt child hc, originAt]
  change (placed.relative.getD g default).contains
    ((placed.relative.getD child default).shift
      ((placed.localGroups.getD child default).x * p.pitchX)
      ((placed.localGroups.getD child default).y * p.pitchY)) at localInside
  simp only [Span.contains, Span.shift, Int.add_mul] at localInside ⊢
  omega

private theorem span_containment_trans (outer middle inner : Span)
    (first : outer.contains middle) (second : middle.contains inner) :
    outer.contains inner := by
  unfold Span.contains at first second ⊢
  omega

theorem group_chain_contains_descendant (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (target : Span) :
    ∀ depth current, current < input.groups.length →
      ((resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD
        current default).contains target →
      ∀ unit ∈ groupChain input.groups depth (Int.ofNat current),
        unit.group.toNat < input.groups.length ∧
          ((resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.getD
            unit.group.toNat default).contains target := by
  intro depth
  induction depth with
  | zero =>
    intro current hc inside unit member
    simp only [groupChain, List.not_mem_nil] at member
  | succ depth ih =>
    intro current hc inside unit member
    have nonnegative : ¬Int.ofNat current < 0 :=
      Int.not_lt.mpr (Int.natCast_nonneg current)
    rw [groupChain, ite_eq_right nonnegative] at member
    simp only [Int.ofNat_eq_natCast, Int.toNat_natCast] at member
    rcases List.mem_append.mp member with ancestor | self
    · let parent := (input.groups.getD current default).parent
      change unit ∈ groupChain input.groups depth parent at ancestor
      by_cases negative : parent < 0
      · cases depth with
        | zero => simp only [groupChain, List.not_mem_nil] at ancestor
        | succ depth =>
          rw [groupChain, ite_eq_left negative] at ancestor
          cases ancestor
      · have parentNonnegative : 0 ≤ parent := by omega
        have order : parent < Int.ofNat current := ordered current hc
        have parentBound : parent.toNat < input.groups.length := by
          simp only [Int.ofNat_eq_natCast] at order
          omega
        have owner : (input.groups.getD current default).parent =
            Int.ofNat parent.toNat := by
          change parent = Int.ofNat parent.toNat
          simp only [Int.ofNat_eq_natCast]
          omega
        have parentInside := resolved_group_contains_child_frame input p fp fuel
          ordered px py padding line current parent.toNat hc parentBound owner
        have combined := span_containment_trans _ _ target parentInside inside
        have parentEq : Int.ofNat parent.toNat = parent := by
          simp only [Int.ofNat_eq_natCast]
          omega
        apply ih parent.toNat parentBound combined unit
        simpa only [parentEq] using ancestor
    · have equal := List.mem_singleton.mp self
      subst unit
      simpa only [Int.toNat_natCast] using And.intro hc inside

theorem node_ancestor_frames_contain_tile (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (n : Nat) (hn : n < (virtualParents input).length) :
    let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
    ∀ unit ∈ groupChain input.groups input.groups.length
        ((virtualParents input).getD n (-1)),
      unit.group.toNat < input.groups.length ∧
        (resolved.frames.getD unit.group.toNat default).contains
          ((⟨0, 0, p.pitchX, p.pitchY⟩ : Span).shift
            ((resolved.nodes.getD n default).x * p.pitchX)
            ((resolved.nodes.getD n default).y * p.pitchY)) := by
  intro resolved unit member
  rcases virtual_parent_admitted input parents n hn with root | grouped
  · rw [root] at member
    cases lengthEq : input.groups.length with
    | zero => simp only [lengthEq, groupChain, List.not_mem_nil] at member
    | succ count =>
      simp only [lengthEq, groupChain, show (-1 : Int) < 0 by decide,
        ↓reduceIte, List.not_mem_nil] at member
  · obtain ⟨g, hg, owner⟩ := grouped
    have inside := resolved_group_contains_node_tile input p fp fuel
      ordered px py padding line n g hn hg owner
    apply group_chain_contains_descendant input p fp fuel ordered px py padding line
      _ input.groups.length g hg inside unit
    simpa only [owner] using member

def UnitOwned (input : Input) (parent : Int) (unit : Unit) : Prop :=
  (unit.group = -1 ∧ ∃ n, n < (virtualParents input).length ∧
    unit.node = Int.ofNat n ∧ (virtualParents input).getD n (-1) = parent) ∨
  (unit.node = -1 ∧ ∃ g, g < input.groups.length ∧
    unit.group = Int.ofNat g ∧ (input.groups.getD g default).parent = parent)

def ParentPath (input : Input) : Int → List Unit → Int → Prop
  | parent, [], finish => parent = finish
  | parent, unit :: rest, finish =>
    UnitOwned input parent unit ∧ ParentPath input unit.group rest finish

private theorem parentPath_append (input : Input) (before suffix : List Unit)
    (start middle finish : Int)
    (left : ParentPath input start before middle)
    (right : ParentPath input middle suffix finish) :
    ParentPath input start (before ++ suffix) finish := by
  induction before generalizing start with
  | nil =>
    change start = middle at left
    subst start
    exact right
  | cons unit rest ih =>
    exact ⟨left.1, ih unit.group left.2⟩

theorem groupChain_parent_path (input : Input)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent) :
    ∀ depth parent,
      (parent = -1 ∨ ∃ g, g < input.groups.length ∧ g < depth ∧ parent = Int.ofNat g) →
      ParentPath input (-1) (groupChain input.groups depth parent) parent := by
  intro depth
  induction depth with
  | zero =>
    intro parent admitted
    rcases admitted with rfl | ⟨g, hg, impossible, equal⟩
    · rfl
    · omega
  | succ depth ih =>
    intro parent admitted
    rcases admitted with rfl | ⟨g, hg, gd, rfl⟩
    · rw [groupChain, ite_eq_left (show (-1 : Int) < 0 by decide)]
      rfl
    · rw [groupChain]
      simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
      rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg g))]
      have earlier := ordered g hg
      have admittedParent :
          (input.groups.getD g default).parent = -1 ∨
            ∃ ancestor, ancestor < input.groups.length ∧ ancestor < depth ∧
              (input.groups.getD g default).parent = Int.ofNat ancestor := by
        rcases groupParents g hg with root | ⟨ancestor, bound, owner⟩
        · exact Or.inl root
        · refine Or.inr ⟨ancestor, bound, ?_, owner⟩
          rw [owner] at earlier
          simp only [Int.ofNat_eq_natCast] at earlier
          omega
      have previous := ih (input.groups.getD g default).parent admittedParent
      apply parentPath_append input _ _ (-1) (input.groups.getD g default).parent (g : Int)
        previous
      exact ⟨Or.inr ⟨rfl, g, hg, rfl, rfl⟩, rfl⟩

theorem chainOf_parent_path (input : Input)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (n : Nat) (hn : n < (virtualParents input).length) :
    ParentPath input (-1) (chainOf input n) (-1) := by
  have admitted := virtual_parent_admitted input parents n hn
  have path := groupChain_parent_path input ordered groupParents input.groups.length
    ((virtualParents input).getD n (-1)) (by
      rcases admitted with root | ⟨g, hg, owner⟩
      · exact Or.inl root
      · exact Or.inr ⟨g, hg, hg, owner⟩)
  apply parentPath_append input _ _ (-1) ((virtualParents input).getD n (-1)) (-1) path
  exact ⟨Or.inl ⟨rfl, n, hn, rfl, rfl⟩, rfl⟩

theorem divergent_units_owned (input : Input) (left right : List Unit)
    (parent leftEnd rightEnd owner : Int) (first second : Unit)
    (leftPath : ParentPath input parent left leftEnd)
    (rightPath : ParentPath input parent right rightEnd)
    (found : divergent left right parent = some (owner, first, second)) :
    UnitOwned input owner first ∧ UnitOwned input owner second := by
  induction left generalizing right parent with
  | nil => cases found
  | cons a rest ih =>
    cases right with
    | nil => cases found
    | cons b tail =>
      by_cases same : a = b
      · subst b
        rw [divergent, ite_eq_left rfl] at found
        exact ih tail a.group leftPath.2 rightPath.2 found
      · rw [divergent, ite_eq_right same] at found
        cases Option.some.inj found
        exact ⟨leftPath.1, rightPath.1⟩

private theorem mapM_outputs_satisfy {α β : Type} (source : List α)
    (f : α → Except LayoutError β) (output : List β) (property : β → Prop)
    (decoded : source.mapM f = .ok output)
    (step : ∀ a ∈ source, ∀ b, f a = .ok b → property b) :
    ∀ b ∈ output, property b := by
  induction source generalizing output with
  | nil =>
    have equal : [] = output := by
      simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using decoded
    subst output
    simp
  | cons a rest ih =>
    cases head : f a with
    | error error =>
      rw [List.mapM_cons, head] at decoded
      cases decoded
    | ok first =>
      rw [List.mapM_cons, head] at decoded
      cases tail : rest.mapM f with
      | error error =>
        rw [tail] at decoded
        cases decoded
      | ok remaining =>
        rw [tail] at decoded
        have equal : first :: remaining = output := Except.ok.inj decoded
        subst output
        intro b member
        rcases List.mem_cons.mp member with same | later
        · subst b
          exact step a List.mem_cons_self first head
        · exact ih remaining tail
            (by intro x present; exact step x (List.mem_cons_of_mem a present)) b later

theorem decoded_group_parent_admission {α : Type}
    (declarations : List ModelBox) (source : List α) (groups : List Group)
    (parentId : α → String) (make : α → Int → Group)
    (make_parent : ∀ a parent, (make a parent).parent = parent)
    (decoded : source.mapM (fun a =>
      (if (parentId a).isEmpty then
        (Except.ok (-1) : Except LayoutError Int)
      else match declarations.findIdx? (fun (b : ModelBox) => b.id == parentId a) with
        | some i => .ok (Int.ofNat i)
        | none => .error .domain).bind (fun parent => pure (make a parent))) = .ok groups) :
    ∀ group ∈ groups, group.parent = -1 ∨
      ∃ parent, parent < declarations.length ∧ group.parent = Int.ofNat parent := by
  refine mapM_outputs_satisfy source _ groups
    (fun group => group.parent = -1 ∨
      ∃ parent, parent < declarations.length ∧ group.parent = Int.ofNat parent)
    decoded ?_
  intro a present group single
  cases empty : (parentId a).isEmpty with
  | true =>
    rw [ite_eq_left empty] at single
    have equal : make a (-1) = group := Except.ok.inj single
    subst group
    exact Or.inl (make_parent a (-1))
  | false =>
    rw [ite_eq_right (by simp only [empty, Bool.false_eq_true, not_false_eq_true])] at single
    cases found : declarations.findIdx? (fun b => b.id == parentId a) with
    | none =>
      rw [found] at single
      cases single
    | some parent =>
      rw [found] at single
      have equal : make a (Int.ofNat parent) = group := Except.ok.inj single
      subst group
      exact Or.inr ⟨parent, (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1,
        make_parent a (Int.ofNat parent)⟩

theorem owned_unit_in_level (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (unit : Unit) (owned : UnitOwned input parent unit) :
    unit ∈ (levelOf input p relative parent).units := by
  rcases owned with ⟨group, n, bound, node, owner⟩ | ⟨node, g, bound, group, owner⟩
  · have equal : unit = (⟨Int.ofNat n, -1⟩ : Unit) := by
      cases unit
      simp_all only
    subst unit
    simpa only [owner] using node_in_own_level input p relative n bound
  · have equal : unit = (⟨-1, Int.ofNat g⟩ : Unit) := by
      cases unit
      simp_all only
    subst unit
    simpa only [owner] using group_in_own_level input p relative g bound

theorem divergent_units_in_level (input : Input) (p : Params) (relative : List Span)
    (a b : Nat) (owner : Int) (first second : Unit)
    (leftPath : ParentPath input (-1) (chainOf input a) (-1))
    (rightPath : ParentPath input (-1) (chainOf input b) (-1))
    (found : divergent (chainOf input a) (chainOf input b) (-1) =
      some (owner, first, second)) :
    first ∈ (levelOf input p relative owner).units ∧
      second ∈ (levelOf input p relative owner).units := by
  have owned := divergent_units_owned input (chainOf input a) (chainOf input b)
    (-1) (-1) (-1) owner first second leftPath rightPath found
  exact ⟨owned_unit_in_level input p relative owner first owned.1,
    owned_unit_in_level input p relative owner second owned.2⟩

private theorem mapM_output_length {α β : Type} (source : List α)
    (f : α → Except LayoutError β) (output : List β)
    (decoded : source.mapM f = .ok output) : source.length = output.length := by
  induction source generalizing output with
  | nil =>
    have equal : [] = output := by
      simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using decoded
    subst output
    rfl
  | cons a rest ih =>
    cases head : f a with
    | error error =>
      rw [List.mapM_cons, head] at decoded
      cases decoded
    | ok first =>
      rw [List.mapM_cons, head] at decoded
      cases tail : rest.mapM f with
      | error error =>
        rw [tail] at decoded
        cases decoded
      | ok remaining =>
        rw [tail] at decoded
        have equal : first :: remaining = output := Except.ok.inj decoded
        subst output
        simp only [List.length_cons, ih remaining tail]


theorem owned_parent_admitted (input : Input)
    (groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (parent : Int) (unit : Unit) (owned : UnitOwned input parent unit) :
    parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
  rcases owned with ⟨group, n, hn, node, owner⟩ | ⟨node, g, hg, group, owner⟩
  · have admitted := virtual_parent_admitted input parents n hn
    simpa only [owner] using admitted
  · have admitted := groupParents g hg
    simpa only [owner] using admitted

private theorem level_sibling_witness (l : Level) (first second : Unit)
    (left : first ∈ l.units) (right : second ∈ l.units) (different : first ≠ second)
    (separated : ∀ i j, i < l.units.length → j < l.units.length → i ≠ j →
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false) :
    ∃ i j, i < l.units.length ∧ j < l.units.length ∧
      l.units[i]? = some first ∧ l.units[j]? = some second ∧ i ≠ j ∧
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false := by
  obtain ⟨i, leftLookup⟩ := List.mem_iff_getElem?.mp left
  obtain ⟨j, rightLookup⟩ := List.mem_iff_getElem?.mp right
  have hi := (List.getElem?_eq_some_iff.mp leftLookup).choose
  have hj := (List.getElem?_eq_some_iff.mp rightLookup).choose
  have indices : i ≠ j := by
    intro equal
    rw [equal, rightLookup] at leftLookup
    exact different (Option.some.inj leftLookup).symm
  exact ⟨i, j, hi, hj, leftLookup, rightLookup, indices,
    separated i j hi hj indices⟩

def SiblingsExecuted (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (owner : Int) (first second : Unit) : Prop :=
  ∃ before,
    (owner = -1 ∧ before = (List.range input.groups.length).reverse ∨
      ∃ g suffix, owner = Int.ofNat g ∧
        (List.range input.groups.length).reverse = before ++ g :: suffix) ∧
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative owner)).1
    ∃ i j, i < l.units.length ∧ j < l.units.length ∧
      l.units[i]? = some first ∧ l.units[j]? = some second ∧ i ≠ j ∧
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false

theorem divergent_siblings_executed (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (a b : Nat) (ha : a < (virtualParents input).length)
    (hb : b < (virtualParents input).length) (different : a ≠ b) :
    ∃ owner first second,
      divergent (chainOf input a) (chainOf input b) (-1) =
        some (owner, first, second) ∧
      SiblingsExecuted input p fp fuel owner first second := by
  obtain ⟨owner, first, second, found⟩ := chainOf_divergent input a b different
  have leftPath := chainOf_parent_path input ordered groupParents parents a ha
  have rightPath := chainOf_parent_path input ordered groupParents parents b hb
  have owned := divergent_units_owned input (chainOf input a) (chainOf input b)
    (-1) (-1) (-1) owner first second leftPath rightPath found
  have distinct := (chainOf_divergent_units input a b owner first second found).1
  refine ⟨owner, first, second, found, ?_⟩
  rcases owned_parent_admitted input groupParents parents owner first owned.1 with root |
      ⟨g, hg, groupOwner⟩
  · subst owner
    let before := (List.range input.groups.length).reverse
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    have members := divergent_units_in_level input p state.relative a b (-1)
      first second leftPath rightPath found
    refine ⟨before, Or.inl ⟨rfl, rfl⟩, ?_⟩
    apply level_sibling_witness l first second
    · simpa only [l, arrange_units] using members.1
    · simpa only [l, arrange_units] using members.2
    · exact distinct
    · exact executed_root_unit_rects_separated input p fp fuel ordered px py padding line
  · subst owner
    obtain ⟨before, suffix, position⟩ :=
      split_member (List.range input.groups.length).reverse g
        (List.mem_reverse.mpr (List.mem_range.mpr hg))
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    have members := divergent_units_in_level input p state.relative a b (Int.ofNat g)
      first second leftPath rightPath found
    refine ⟨before, Or.inr ⟨g, suffix, rfl, position⟩, ?_⟩
    apply level_sibling_witness l first second
    · simpa only [l, arrange_units] using members.1
    · simpa only [l, arrange_units] using members.2
    · exact distinct
    · exact executed_group_unit_rects_separated input p fp fuel ordered px py padding line
        before suffix g position

theorem prefix_storage_lengths (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) (before : List Nat) :
    (afterPrefix input p fp fuel before).localNodes.length = (virtualParents input).length ∧
      (afterPrefix input p fp fuel before).localGroups.length = input.groups.length ∧
      (afterPrefix input p fp fuel before).relative.length = input.groups.length := by
  have fold : ∀ (indices : List Nat) (seed : Placement),
      let final := indices.foldl
        (fun seed k => arrangeParent input p fp (Int.ofNat k) seed) seed
      final.localNodes.length = seed.localNodes.length ∧
        final.localGroups.length = seed.localGroups.length ∧
        final.relative.length = seed.relative.length := by
    intro indices
    induction indices with
    | nil => intro seed; exact ⟨rfl, rfl, rfl⟩
    | cons k rest ih =>
      intro seed
      have step := arrangeParent_storage_lengths input p fp (Int.ofNat k) seed
      have tail := ih (arrangeParent input p fp (Int.ofNat k) seed)
      exact ⟨tail.1.trans step.1, tail.2.1.trans step.2.1,
        tail.2.2.trans step.2.2⟩
  have lengths := fold before (initial input fuel)
  exact ⟨lengths.1.trans (List.length_replicate ..),
    lengths.2.1.trans (List.length_replicate ..),
    lengths.2.2.trans (List.length_replicate ..)⟩

theorem executed_owner_unit_storage (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (parent : Int) (before : List Nat)
    (executed : parent = -1 ∧ before = (List.range input.groups.length).reverse ∨
      ∃ g suffix, parent = Int.ofNat g ∧
        (List.range input.groups.length).reverse = before ++ g :: suffix) :
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative parent)).1
    ∀ q ∈ l.units.zipIdx,
      (q.1.group < 0 →
        (placeHierarchy input p fp fuel).localNodes.getD q.1.node.toNat default =
          l.cells.getD q.2 default) ∧
      (0 ≤ q.1.group →
        (placeHierarchy input p fp fuel).localGroups.getD q.1.group.toNat default =
            l.cells.getD q.2 default ∧
          (placeHierarchy input p fp fuel).relative.getD q.1.group.toNat default =
            state.relative.getD q.1.group.toNat default) := by
  intro state l q member
  have lengths := prefix_storage_lengths input p fp fuel before
  rcases executed with root | grouped
  · rcases root with ⟨rfl, rfl⟩
    constructor
    · intro node
      exact (arrangeParent_node_placement input p fp (-1) state lengths.1 q member node).1
    · intro group
      constructor
      · exact arrangeParent_group_placement input p fp (-1) state lengths.2.1 q member group
      · change (arrangeParent input p fp (-1) state).relative.getD q.1.group.toNat default = _
        rw [arrangeParent_relative]
        rfl
  · obtain ⟨g, suffix, rfl, position⟩ := grouped
    have decreasing :
        ((List.range input.groups.length).reverse).Pairwise (fun a b => b < a) :=
      List.pairwise_reverse.mpr List.pairwise_lt_range
    rw [position] at decreasing
    have lower : ∀ k ∈ suffix, k < g :=
      (List.pairwise_cons.mp (List.pairwise_append.mp decreasing).2.1).1
    have hierarchy : placeHierarchy input p fp fuel =
        arrangeParent input p fp (-1)
          (suffix.foldl (fun seed k => arrangeParent input p fp (Int.ofNat k) seed)
            (arrangeParent input p fp (Int.ofNat g) state)) := by
      change arrangeParent input p fp (-1)
        (((List.range input.groups.length).reverse).foldl
          (fun seed k => arrangeParent input p fp (Int.ofNat k) seed)
          (initial input fuel)) = _
      rw [position, List.foldl_append, List.foldl_cons]
      rfl
    constructor
    · intro node
      rw [hierarchy]
      exact group_node_placement_survives_suffix input p fp g suffix lower state
        lengths.1 q member node
    · intro group
      have original : q.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
        have present : q.1 ∈ l.units :=
          List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
        simpa only [l, arrange_units] using present
      have owner := level_group_owner input p state.relative (Int.ofNat g) q.1 original group
      have order := ordered q.1.group.toNat owner.1
      rw [owner.2] at order
      have afterParent : g < q.1.group.toNat := by
        simp only [Int.ofNat_eq_natCast] at order
        omega
      rw [hierarchy]
      constructor
      · rw [arrangeParent_preserves_foreign_group input p fp (-1) _ q.1.group.toNat
          (by rw [owner.2]; simp only [Int.ofNat_eq_natCast]; omega)]
        rw [hierarchy_fold_preserves_foreign_group input p fp suffix _ q.1.group.toNat (by
          intro k present
          have bound := lower k present
          rw [owner.2]
          simp only [Int.ofNat_eq_natCast]
          omega)]
        exact arrangeParent_group_placement input p fp (Int.ofNat g) state lengths.2.1
          q member group
      · rw [arrangeParent_relative]
        simp only [show (-1 : Int) < 0 by decide, ↓reduceIte]
        rw [hierarchy_fold_preserves_other_frame input p fp suffix _ q.1.group.toNat (by
          intro k present
          have bound := lower k present
          omega)]
        exact arrangeParent_preserves_other_frame input p fp g q.1.group.toNat state (by omega)

def resolvedUnitSpan (p : Params) (resolved : Resolved) (unit : Unit) : Span :=
  if unit.group < 0 then
    (⟨0, 0, p.pitchX, p.pitchY⟩ : Span).shift
      ((resolved.nodes.getD unit.node.toNat default).x * p.pitchX)
      ((resolved.nodes.getD unit.node.toNat default).y * p.pitchY)
  else resolved.frames.getD unit.group.toNat default

theorem executed_owner_level_invariant (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (parent : Int) (before : List Nat)
    (executed : parent = -1 ∧ before = (List.range input.groups.length).reverse ∨
      ∃ g suffix, parent = Int.ofNat g ∧
        (List.range input.groups.length).reverse = before ++ g :: suffix) :
    let state := afterPrefix input p fp fuel before
    LevelInvariant p (arrange p state.fuel (levelOf input p state.relative parent)).1 := by
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  rcases executed with ⟨rfl, rfl⟩ | ⟨g, suffix, rfl, position⟩
  · have root := hierarchyRunEvidence_after_prefix input p fp
      (List.range input.groups.length).reverse [] (initial input fuel)
      (by simpa only [List.append_nil, initial] using full)
    exact root.1
  · rw [position] at full
    exact (hierarchyRunEvidence_after_prefix input p fp before (g :: suffix)
      (initial input fuel) full).1

theorem executed_owner_final_spans (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (parent : Int) (before : List Nat)
    (executed : parent = -1 ∧ before = (List.range input.groups.length).reverse ∨
      ∃ g suffix, parent = Int.ofNat g ∧
        (List.range input.groups.length).reverse = before ++ g :: suffix) :
    let state := afterPrefix input p fp fuel before
    let l := (arrange p state.fuel (levelOf input p state.relative parent)).1
    let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
    ∃ dx dy : Int, ∀ q ∈ l.units.zipIdx,
      resolvedUnitSpan p resolved q.1 = (l.absolute.getD q.2 default).shift dx dy := by
  intro state l resolved
  let placed := placeHierarchy input p fp fuel
  obtain ⟨origins, originLength, originEquations, frames, nodes⟩ :=
    resolveHierarchy_execution input p placed ordered
  let base : Cell := if parent < 0 then default else origins.getD parent.toNat default
  refine ⟨base.x * p.pitchX, base.y * p.pitchY, ?_⟩
  intro q member
  have storage := executed_owner_unit_storage input p fp fuel ordered parent before executed q member
  change (q.1.group < 0 → placed.localNodes.getD q.1.node.toNat default =
      l.cells.getD q.2 default) ∧
    (0 ≤ q.1.group → placed.localGroups.getD q.1.group.toNat default =
        l.cells.getD q.2 default ∧
      placed.relative.getD q.1.group.toNat default =
        state.relative.getD q.1.group.toNat default) at storage
  have invariant := executed_owner_level_invariant input p fp fuel ordered px py
    padding line parent before executed
  have lookup := List.mem_zipIdx_iff_getElem?.mp member
  have bound := (List.getElem?_eq_some_iff.mp lookup).choose
  have sourceLookup : (levelOf input p state.relative parent).units[q.2]? = some q.1 := by
    simpa only [l, arrange_units] using lookup
  have sourceBound : q.2 < (levelOf input p state.relative parent).units.length := by
    simpa only [l, arrange_units] using bound
  have marked := arranged_parent_all_placed input p state.relative parent state.fuel q.2 sourceBound
  have coordinates := invariant.2.1.2.2 q.2
    (by rw [arrange_placed_length, level_placed_length]; exact sourceBound) marked
  change l.absolute.getD q.2 default =
    (l.rects.getD q.2 default).shift
      ((l.cells.getD q.2 default).x * p.pitchX)
      ((l.cells.getD q.2 default).y * p.pitchY) at coordinates
  have rectLookup : l.rects[q.2]? = some
      (if q.1.group < 0 then (⟨0, 0, p.pitchX, p.pitchY⟩ : Span)
      else state.relative.getD q.1.group.toNat default) := by
    rw [arrange_rects]
    change ((levelOf input p state.relative parent).units.map (fun u =>
      if u.group < 0 then (⟨0, 0, p.pitchX, p.pitchY⟩ : Span)
      else state.relative.getD u.group.toNat default))[q.2]? = _
    rw [List.getElem?_map, sourceLookup]
    rfl
  have rectAt : l.rects.getD q.2 default =
      if q.1.group < 0 then (⟨0, 0, p.pitchX, p.pitchY⟩ : Span)
      else state.relative.getD q.1.group.toNat default := by
    simp only [List.getD_eq_getElem?_getD, rectLookup, Option.getD_some]
  have original := List.mem_of_getElem? sourceLookup
  by_cases node : q.1.group < 0
  · have owner := level_node_owner input p state.relative parent q.1 original node
    have nodeAt : resolved.nodes.getD q.1.node.toNat default =
        (⟨base.x + (l.cells.getD q.2 default).x,
          base.y + (l.cells.getD q.2 default).y⟩ : Cell) := by
      change (resolveHierarchy input p placed).nodes.getD q.1.node.toNat default = _
      rw [nodes, indexed_map_at _ _ q.1.node.toNat (-1) default owner.1, owner.2]
      change (⟨base.x + (placed.localNodes.getD q.1.node.toNat default).x,
        base.y + (placed.localNodes.getD q.1.node.toNat default).y⟩ : Cell) = _
      rw [storage.1 node]
    rw [resolvedUnitSpan, ite_eq_left node, nodeAt, coordinates, rectAt, ite_eq_left node]
    simp only [Span.shift, Int.add_mul, Span.mk.injEq]
    omega
  · have group : 0 ≤ q.1.group := by omega
    have owner := level_group_owner input p state.relative parent q.1 original group
    have groupStored := storage.2 group
    have frameAt : resolved.frames.getD q.1.group.toNat default =
        (placed.relative.getD q.1.group.toNat default).shift
          ((origins.getD q.1.group.toNat default).x * p.pitchX)
          ((origins.getD q.1.group.toNat default).y * p.pitchY) := by
      change (resolveHierarchy input p placed).frames.getD q.1.group.toNat default = _
      rw [frames, indexed_map_at _ _ q.1.group.toNat default default (by
        rw [show placed.relative.length = input.groups.length from
          hierarchy_relative_length input p fp fuel]
        exact owner.1)]
    have groupLookup : input.groups[q.1.group.toNat]? =
        some (input.groups.getD q.1.group.toNat default) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem owner.1,
        Option.getD_some]
    have originAt := originEquations
      (input.groups.getD q.1.group.toNat default, q.1.group.toNat)
      (List.mem_zipIdx_iff_getElem?.mpr groupLookup)
    change origins.getD q.1.group.toNat default =
      (⟨(if (input.groups.getD q.1.group.toNat default).parent < 0 then
            (default : Cell) else origins.getD
            (input.groups.getD q.1.group.toNat default).parent.toNat default).x +
          (placed.localGroups.getD q.1.group.toNat default).x,
        (if (input.groups.getD q.1.group.toNat default).parent < 0 then
            (default : Cell) else origins.getD
            (input.groups.getD q.1.group.toNat default).parent.toNat default).y +
          (placed.localGroups.getD q.1.group.toNat default).y⟩ : Cell) at originAt
    rw [owner.2] at originAt
    change origins.getD q.1.group.toNat default =
      (⟨base.x + (placed.localGroups.getD q.1.group.toNat default).x,
        base.y + (placed.localGroups.getD q.1.group.toNat default).y⟩ : Cell) at originAt
    rw [groupStored.1] at originAt
    rw [resolvedUnitSpan, ite_eq_right node, frameAt, originAt, groupStored.2,
      coordinates, rectAt, ite_eq_right node]
    simp only [Span.shift, Int.add_mul, Span.mk.injEq]
    omega

theorem executed_sibling_final_spans_separated (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (owner : Int) (first second : Unit)
    (siblings : SiblingsExecuted input p fp fuel owner first second) :
    let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
    (resolvedUnitSpan p resolved first).overlaps
      (resolvedUnitSpan p resolved second) = false := by
  obtain ⟨before, executed, i, j, hi, hj, leftLookup, rightLookup, different, separated⟩ :=
    siblings
  let state := afterPrefix input p fp fuel before
  let l := (arrange p state.fuel (levelOf input p state.relative owner)).1
  obtain ⟨dx, dy, transported⟩ := executed_owner_final_spans input p fp fuel
    ordered px py padding line owner before executed
  have leftIndexed : (first, i) ∈ l.units.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr leftLookup
  have rightIndexed : (second, j) ∈ l.units.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr rightLookup
  have left := transported (first, i) leftIndexed
  have right := transported (second, j) rightIndexed
  change (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
    first).overlaps
    (resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
      second) = false
  change resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
    first = (l.absolute.getD i default).shift dx dy at left
  change resolvedUnitSpan p (resolveHierarchy input p (placeHierarchy input p fp fuel))
    second = (l.absolute.getD j default).shift dx dy at right
  change (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false at separated
  rw [left, right]
  exact separated_subtrees_after_origin_shift _ _ _ _ dx dy separated
    ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩
    ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩

theorem chain_unit_contains_node_tile (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (n : Nat) (hn : n < (virtualParents input).length)
    (unit : Unit) (member : unit ∈ chainOf input n) :
    let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
    (resolvedUnitSpan p resolved unit).contains
      (resolvedUnitSpan p resolved (⟨Int.ofNat n, -1⟩ : Unit)) := by
  intro resolved
  rcases chainOf_unit_cases input n unit member with group | terminal
  · have ancestor : unit ∈ groupChain input.groups input.groups.length
        ((virtualParents input).getD n (-1)) := by
      rcases List.mem_append.mp member with ancestor | terminal
      · exact ancestor
      · have equal := List.mem_singleton.mp terminal
        subst unit
        change (0 : Int) ≤ -1 at group
        omega
    have inside := (node_ancestor_frames_contain_tile input p fp fuel ordered px py
      padding line parents n hn unit ancestor).2
    simpa only [resolvedUnitSpan, ite_eq_right (Int.not_lt.mpr group),
      show (-1 : Int) < 0 by decide, ↓reduceIte,
      Int.ofNat_eq_natCast, Int.toNat_natCast] using inside
  · subst unit
    simp only [Int.ofNat_eq_natCast]
    exact ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩

theorem hierarchy_final_cells_distinct (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (a b : Nat) (ha : a < (virtualParents input).length)
    (hb : b < (virtualParents input).length) (different : a ≠ b) :
    (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD a default ≠
      (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD b default := by
  let resolved := resolveHierarchy input p (placeHierarchy input p fp fuel)
  obtain ⟨owner, first, second, found, siblings⟩ :=
    divergent_siblings_executed input p fp fuel ordered groupParents parents
      px py padding line a b ha hb different
  have separated := executed_sibling_final_spans_separated input p fp fuel
    ordered px py padding line owner first second siblings
  have members := chainOf_divergent_units input a b owner first second found
  have leftInside := chain_unit_contains_node_tile input p fp fuel ordered px py
    padding line parents a ha first members.2.1
  have rightInside := chain_unit_contains_node_tile input p fp fuel ordered px py
    padding line parents b hb second members.2.2.1
  have tilesSeparated := separated_subtrees_after_origin_shift _ _ _ _ 0 0
    separated leftInside rightInside
  simp only [Span.shift, Int.add_zero] at tilesSeparated
  change (resolvedUnitSpan p resolved (⟨Int.ofNat a, -1⟩ : Unit)).overlaps
    (resolvedUnitSpan p resolved (⟨Int.ofNat b, -1⟩ : Unit)) = false at tilesSeparated
  simp only [resolvedUnitSpan, show (-1 : Int) < 0 by decide, ↓reduceIte,
    Int.ofNat_eq_natCast, Int.toNat_natCast] at tilesSeparated
  intro equal
  change resolved.nodes.getD a default = resolved.nodes.getD b default at equal
  rw [equal] at tilesSeparated
  unfold Span.overlaps at tilesSeparated
  have impossible := decide_eq_false_iff_not.mp tilesSeparated
  apply impossible
  simp only [Span.shift]
  omega

theorem hierarchy_final_cells_unique (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent)
    (parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  have length := (resolveHierarchy_storage_lengths input p fp fuel).1
  have ibound : i < (virtualParents input).length := by omega
  have jbound : j < (virtualParents input).length := by omega
  have distinct := hierarchy_final_cells_distinct input p fp fuel ordered groupParents
    parents px py padding line i j ibound jbound (by omega)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] using distinct

private theorem checked_config_integer_nonnegative
    (source : Option (String × ConfigValue)) (n : Int)
    (decoded : (match source with
      | some (_, .integer value) =>
        if 0 ≤ value ∧ value ≤ I32_MAX then some value else none
      | _ => none) = some n) : 0 ≤ n := by
  cases source with
  | none => cases decoded
  | some pair =>
    obtain ⟨key, value⟩ := pair
    cases value with
    | string value => cases decoded
    | boolean value => cases decoded
    | integer value =>
      change (if 0 ≤ value ∧ value ≤ I32_MAX then some value else none) = some n at decoded
      by_cases valid : 0 ≤ value ∧ value ≤ I32_MAX
      · rw [ite_eq_left valid] at decoded
        have same := Option.some.inj decoded
        rw [← same]
        exact valid.1
      · rw [ite_eq_right valid] at decoded
        cases decoded

private theorem decoded_frame_padding_nonnegative
    (m : Model) (profile : Profile) (cell : Bool) (padding : Int)
    (decoded : padding = (match
        (match m.options.config.find? (fun q => q.1 == "padding") with
          | some (_, .integer value) =>
            if 0 ≤ value ∧ value ≤ I32_MAX then some value else none
          | _ => none) with
      | some px => if cell then Int.fdiv (2 * px + 20) 40 else px * 64
      | none => LayoutConst.architecture_padding.get profile)) :
    0 ≤ padding := by
  let value : Option Int :=
    match m.options.config.find? (fun q => q.1 == "padding") with
    | some (_, .integer value) =>
      if 0 ≤ value ∧ value ≤ I32_MAX then some value else none
    | _ => none
  change padding = (match value with
    | some px => if cell then Int.fdiv (2 * px + 20) 40 else px * 64
    | none => LayoutConst.architecture_padding.get profile) at decoded
  cases actual : value with
  | none =>
    rw [actual] at decoded
    rw [decoded]
    change 0 ≤ LayoutConst.architecture_padding.get profile
    cases profile <;> decide
  | some px =>
    have sourceNonnegative := checked_config_integer_nonnegative
      (m.options.config.find? (fun q => q.1 == "padding")) px actual
    rw [actual] at decoded
    rw [decoded]
    cases cell with
    | false =>
      change 0 ≤ px * 64
      exact Int.mul_nonneg sourceNonnegative (by decide)
    | true =>
      change 0 ≤ Int.fdiv (2 * px + 20) 40
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
      exact Int.ediv_nonneg (by omega) (by decide)

private theorem native_pitch_floor_bounds (gp : GeometryParams)
    (nodes : List Node) (sizes : List Size) :
    gp.pitchX ≤ (Architecture.pitch gp nodes sizes).x ∧
      gp.pitchY ≤ (Architecture.pitch gp nodes sizes).y := by
  unfold Architecture.pitch
  dsimp only
  constructor
  · split <;> omega
  · omega

def SceneCellExecution (m : Model) (scene : Scene)
    (input : Input) (p : Params) (fp : FrameParams) : Prop :=
  ∃ (gp : GeometryParams) (nativePitch : Pitch) (nodeInput : List Node)
      (groupInput : List Group) (dx dy : Int) (boxes frames : List Rect),
    input.parents = nodeInput.map (·.parent) ∧ input.groups = groupInput ∧
    nodeInput.length = (m.boxes.filter (fun b => b.role != .group)).length ∧
    groupInput.length = (m.boxes.filter (fun b => b.role == .group)).length ∧
    p.pitchX = nativePitch.x ∧ p.pitchY = nativePitch.y ∧
    let resolved := resolveHierarchy input p
      (placeHierarchy input p fp (LayoutConst.architecture_bfs_cap.get m.profile).toNat)
    let geo := Architecture.geometry gp nativePitch nodeInput groupInput resolved
    geo.boxes.mapM (translateRect dx dy) = .ok boxes ∧
    geo.frames.mapM (translateRect dx dy) = .ok frames ∧
    m.boxes.mapM (fun (b : ModelBox) => do
      let r ← if b.role == BoxRole.group then
        match (m.boxes.filter (fun (b : ModelBox) => b.role == BoxRole.group)).findIdx?
            (fun (q : ModelBox) => q.id == b.id) with
        | some i => pure (frames.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      else
        match (m.boxes.filter (fun (b : ModelBox) => b.role != BoxRole.group)).findIdx?
            (fun (q : ModelBox) => q.id == b.id) with
        | some i => pure (boxes.getD i ⟨0, 0, 0, 0⟩)
        | none => throw LayoutError.domain
      pure ({
        id := b.id
        role := b.role.id
        parent := b.parent
        exclusive := b.exclusive
        rect := r } : _root_.Box)) =
      (Except.ok scene.boxes : Except LayoutError (List _root_.Box))

theorem public_build_native_cells_unique (m : Model) (scene : Scene) (capped : Bool)
    (success : Kinds.Architecture.build m = .ok (scene, capped)) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      capped = (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat).budgetExhausted ∧
      SceneCellExecution m scene input p fp ∧
      (∀ g, g < input.groups.length →
        (input.groups.getD g default).parent < Int.ofNat g) ∧
      (∀ g, g < input.groups.length →
        (input.groups.getD g default).parent = -1 ∨
          ∃ parent, parent < input.groups.length ∧
            (input.groups.getD g default).parent = Int.ofNat parent) ∧
      (∀ parent ∈ input.parents,
        parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g) ∧
      (∀ n, n < (virtualParents input).length →
        ParentPath input (-1) (chainOf input n) (-1)) ∧
      0 < p.pitchX ∧ 0 < p.pitchY ∧ 0 ≤ fp.padding ∧ 0 ≤ fp.lineHeight ∧
      (resolveHierarchy input p
        (placeHierarchy input p fp
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat)).nodes.Nodup := by
  obtain ⟨profile, cell, lh, inset, thickness, border, corner, iw, ih,
    padding, gp, groups, nodes, metric, titles, captions, inner, edgeTexts,
    edgeLines, groupInput, nodeInput, edges, input, sizes, pitch, params,
    frameParams, placed, resolved, geometry, rawRoutes, rawBounds, bounds0,
    bounds, margin, dx, dy, width, height, rawLabels, boxes, icons, labels,
    frames, titleRects, edgeRects, routes, dumpBoxes, dumpRoutes, dumpLabels,
    items, facts⟩ := Kinds.Architecture.build_success m scene capped success
  rcases facts with ⟨hprofile, hcell, hlh, hinset, hthickness, hborder,
    hcorner, hiw, hih, hpadding, hp, hgroups, hnodes, hmetric, htitles,
    hcaptions, hinner, hedgeTexts, hedgeLines, hgroupInput, hgroupOrder,
    hnodeInput, hedges, hinput, hsizes, hpitch, hparams, hframeParams, hguard,
    hplaced, hresolved, hgeometry, hrawRoutes, hrawBounds, hbounds0,
    hmargin, hrawLabels, hbounds, hdx, hdy, hwidth, hheight, hsize,
    hboxes, hicons, hlabels, hframes, htitleRects, hedgeRects, hroutes,
    hdumpBoxes, hdumpRoutes, hdumpLabels, hitems, hscene, hcapped⟩
  have groupLength : groupInput.length = groups.length := by
    have titleLength := mapM_output_length groups _ titles htitles
    have decodedLength := mapM_output_length (groups.zip titles) _ groupInput hgroupInput
    rw [List.length_zip, ← titleLength, Nat.min_self] at decodedLength
    exact decodedLength.symm
  have groupAdmission : ∀ group ∈ groupInput, group.parent = -1 ∨
      ∃ parent, parent < groupInput.length ∧ group.parent = Int.ofNat parent := by
    rw [groupLength]
    refine decoded_group_parent_admission groups (groups.zip titles) groupInput
      (fun q => q.1.parent) _ ?_ hgroupInput
    intros
    rfl
  have groupParents : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent = -1 ∨
        ∃ parent, parent < input.groups.length ∧
          (input.groups.getD g default).parent = Int.ofNat parent := by
    rw [hinput]
    intro g hg
    apply groupAdmission
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
      Option.getD_some] using List.getElem_mem hg
  have ordered : ∀ g, g < input.groups.length →
      (input.groups.getD g default).parent < Int.ofNat g := by
    rw [hinput]
    intro g hg
    change (groupInput.getD g default).parent < Int.ofNat g
    have indexed : (groupInput.getD g default, g) ∈ groupInput.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg,
        Option.getD_some]
    apply Classical.byContradiction
    intro notEarlier
    simp only [Int.ofNat_eq_natCast] at notEarlier
    apply hgroupOrder
    apply List.any_eq_true.mpr
    refine ⟨(groupInput.getD g default, g), indexed, ?_⟩
    simp only [decide_eq_true_eq, Int.ofNat_eq_natCast]
    omega
  have parents : ∀ parent ∈ input.parents,
      parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g := by
    rw [hinput]
    change ∀ parent ∈ nodeInput.map (·.parent),
      parent = -1 ∨ ∃ g, g < groupInput.length ∧ parent = Int.ofNat g
    rw [groupLength]
    refine decoded_node_parents groups (nodes.zip captions) nodeInput
      (fun q => q.1.parent)
      (fun q parent =>
        let junction := (q.1.shape.splitOn ";").head! == "junction"
        let size := if junction then LayoutConst.architecture_junction_size.get profile else iw
        let height := if junction then size else ih
        { parent := parent, junction := junction, icon := { w := size, h := height },
          label := ⟨min COORD_LIMIT (Kinds.Common.widest q.2),
            min COORD_LIMIT ((q.2.length : Int) * lh)⟩ })
      (by intros; rfl) hnodeInput
  have basePositive : 0 < gp.pitchX ∧ 0 < gp.pitchY := by
    rw [hp]
    change 0 < LayoutConst.architecture_pitch_x.get profile ∧
      0 < LayoutConst.architecture_pitch_y.get profile
    cases profile <;> decide
  have floorBounds := native_pitch_floor_bounds gp nodeInput sizes
  have pitchPositive : 0 < params.pitchX ∧ 0 < params.pitchY := by
    rw [hparams, hpitch]
    change 0 < (Architecture.pitch gp nodeInput sizes).x ∧
      0 < (Architecture.pitch gp nodeInput sizes).y
    exact ⟨by omega, by omega⟩
  have paddingNonnegative : 0 ≤ frameParams.padding := by
    rw [hframeParams]
    exact decoded_frame_padding_nonnegative m profile cell padding hpadding
  have lineNonnegative : 0 ≤ frameParams.lineHeight := by
    rw [hframeParams, hlh]
    change 0 ≤ LayoutConst.line_h.get profile
    cases profile <;> decide
  have nodeLength : nodeInput.length = nodes.length := by
    have captionLength := mapM_output_length nodes _ captions hcaptions
    have decodedLength := mapM_output_length (nodes.zip captions) _ nodeInput hnodeInput
    rw [List.length_zip, ← captionLength, Nat.min_self] at decodedLength
    exact decodedLength.symm
  have resolvedEq : resolveHierarchy input params
      (placeHierarchy input params frameParams
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat) = resolved := by
    rw [← hprofile, ← hplaced, ← hresolved]
  have sceneExecution : SceneCellExecution m scene input params frameParams := by
    refine ⟨gp, pitch, nodeInput, groupInput, dx, dy, boxes, frames,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hinput]
    · rw [hinput]
    · simpa only [hnodes] using nodeLength
    · simpa only [hgroups] using groupLength
    · rw [hparams]
    · rw [hparams]
    · change (Architecture.geometry gp pitch nodeInput groupInput
        (resolveHierarchy input params (placeHierarchy input params frameParams
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat))).boxes.mapM
        (translateRect dx dy) = .ok boxes
      rw [resolvedEq, ← hgeometry]
      exact hboxes
    · change (Architecture.geometry gp pitch nodeInput groupInput
        (resolveHierarchy input params (placeHierarchy input params frameParams
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat))).frames.mapM
        (translateRect dx dy) = .ok frames
      rw [resolvedEq, ← hgeometry]
      exact hframes
    · rw [hitems, ← hgroups, ← hnodes]
      refine Eq.trans ?_ hdumpBoxes
      apply congrArg (fun f : ModelBox → Except LayoutError _root_.Box => m.boxes.mapM f)
      funext b
      by_cases role : (b.role == BoxRole.group) = true
      · cases found : groups.findIdx? (fun q => q.id == b.id) with
        | none =>
          simp only [role, ite_true, bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw]
        | some i =>
          simp only [role, ite_true, pure, Except.pure, bind, Except.bind]
      · cases found : nodes.findIdx? (fun q => q.id == b.id) with
        | none =>
          simp only [role, Bool.false_eq_true, ite_false, bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw]
        | some i =>
          simp only [role, Bool.false_eq_true, ite_false, pure, Except.pure, bind, Except.bind]
  refine ⟨input, params, frameParams, ?_, sceneExecution, ordered, groupParents, parents,
    chainOf_parent_path input ordered groupParents parents,
    pitchPositive.1, pitchPositive.2, paddingNonnegative, lineNonnegative, ?_⟩
  · simp only [hplaced, hprofile]
  · exact hierarchy_final_cells_unique input params frameParams
      (LayoutConst.architecture_bfs_cap.get m.profile).toNat ordered groupParents
      parents pitchPositive.1 pitchPositive.2 paddingNonnegative lineNonnegative

theorem public_build_source_parent_paths (m : Model) (scene : Scene) (capped : Bool)
    (success : Kinds.Architecture.build m = .ok (scene, capped)) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      capped = (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat).budgetExhausted ∧
      (∀ g, g < input.groups.length →
        (input.groups.getD g default).parent < Int.ofNat g) ∧
      (∀ g, g < input.groups.length →
        (input.groups.getD g default).parent = -1 ∨
          ∃ parent, parent < input.groups.length ∧
            (input.groups.getD g default).parent = Int.ofNat parent) ∧
      (∀ parent ∈ input.parents,
        parent = -1 ∨ ∃ g, g < input.groups.length ∧ parent = Int.ofNat g) ∧
      (∀ n, n < (virtualParents input).length →
        ParentPath input (-1) (chainOf input n) (-1)) := by
  obtain ⟨input, p, fp, cap, execution, ordered, groupParents, parents, paths, rest⟩ :=
    public_build_native_cells_unique m scene capped success
  exact ⟨input, p, fp, cap, ordered, groupParents, parents, paths⟩

theorem arch_cells_unique (m : Model) (result : Layered.FamilyResult)
    (success : Kinds.Architecture.layout m = .ok result) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      result.budgetExhausted = (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat).budgetExhausted ∧
      SceneCellExecution m result.scene input p fp ∧
      0 < p.pitchX ∧ 0 < p.pitchY ∧ 0 ≤ fp.padding ∧ 0 ≤ fp.lineHeight ∧
      (resolveHierarchy input p
        (placeHierarchy input p fp
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat)).nodes.Nodup := by
  unfold Kinds.Architecture.layout at success
  by_cases nodes : m.boxes.length > m.options.limits.maxNodes
  · simp [nodes, bind, Except.bind, throw] at success
  · simp only [nodes, ↓reduceIte, bind, Except.bind, pure, Except.pure] at success
    by_cases edges : m.routes.length > m.options.limits.maxEdges
    · simp [edges, throw] at success
    · simp only [edges, ↓reduceIte] at success
      split at success
      · simp [throw] at success
      · cases built : Kinds.Architecture.build m with
        | error error => simp [built, throw] at success
        | ok pair =>
          obtain ⟨scene, capped⟩ := pair
          have equal : result = {
              scene := scene.projectCellAttachments (Kinds.Common.routeMarkers m)
              budgetExhausted := capped } := by
            simpa only [built, pure, Except.pure, Except.ok.injEq] using success.symm
          subst result
          obtain ⟨input, p, fp, cap, execution, ordered, groupParents, parents, paths,
            px, py, padding, line, unique⟩ :=
            public_build_native_cells_unique m scene capped built
          have preserved : (scene.projectCellAttachments (Kinds.Common.routeMarkers m)).boxes =
              scene.boxes := by
            unfold Scene.projectCellAttachments
            split <;> rfl
          have finalExecution : SceneCellExecution m
              (scene.projectCellAttachments (Kinds.Common.routeMarkers m)) input p fp := by
            simpa only [SceneCellExecution, preserved] using execution
          exact ⟨input, p, fp, cap, finalExecution, px, py, padding, line, unique⟩

theorem arch_cells_execution (m : Model) (result : Layered.FamilyResult)
    (success : Kinds.Architecture.layout m = .ok result) :
    ∃ (input : Input) (p : Params) (fp : FrameParams),
      result.budgetExhausted = (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat).budgetExhausted ∧
      SceneCellExecution m result.scene input p fp ∧
      0 < p.pitchX ∧ 0 < p.pitchY ∧ 0 ≤ fp.padding ∧ 0 ≤ fp.lineHeight ∧
      (resolveHierarchy input p (placeHierarchy input p fp
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat)).nodes.Nodup ∧
      (∀ n, n < (virtualParents input).length →
        NodeExecuted input p fp
          (LayoutConst.architecture_bfs_cap.get m.profile).toNat n) ∧
      (LayoutConst.architecture_bfs_cap.get m.profile).toNat -
          (placeHierarchy input p fp
            (LayoutConst.architecture_bfs_cap.get m.profile).toNat).fuel ≤
        (virtualParents input).length + input.groups.length ∧
      (LayoutConst.architecture_bfs_cap.get m.profile).toNat -
          (placeHierarchy input p fp
            (LayoutConst.architecture_bfs_cap.get m.profile).toNat).fuel ≤
        (LayoutConst.architecture_bfs_cap.get m.profile).toNat := by
  obtain ⟨scene, capped, built, sceneEq, cappedEq⟩ :=
    public_layout_build m result success
  obtain ⟨input, p, fp, cap, execution, ordered, groupParents, parents, paths,
    px, py, padding, line, unique⟩ :=
    public_build_native_cells_unique m scene capped built
  have boxesEq : result.scene.boxes = scene.boxes := by
    rw [sceneEq]
    unfold Scene.projectCellAttachments
    split <;> rfl
  have sceneExecution : SceneCellExecution m result.scene input p fp := by
    simpa only [SceneCellExecution, boxesEq] using execution
  have coverage := source_node_execution_coverage input p fp
    (LayoutConst.architecture_bfs_cap.get m.profile).toNat parents
  have pops := arch_pops_bounded input p fp
    (LayoutConst.architecture_bfs_cap.get m.profile).toNat
  exact ⟨input, p, fp, cappedEq.trans cap, sceneExecution, px, py, padding, line,
    unique, coverage, pops.1, pops.2⟩

end Elegant.Grid.Architecture.CellContracts
