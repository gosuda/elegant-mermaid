import Elegant.Kinds.UsecaseValidExact
import Elegant.Layered.GroupTitleFirstTextProof

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

open Layered Layered.PipelineImpl

private theorem same_key_of_nodup {α : Type} (key : α → String) {xs : List α}
    (hkeys : (xs.map key).Nodup) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs)
    (hk : key a = key b) : a = b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  have he : (xs.map key)[i]? = (xs.map key)[j]? := by
    simp only [List.getElem?_map, hi, hj, Option.map_some, hk]
  have hib : i < (xs.map key).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hi).1
  rw [(List.Nodup.getElem?_inj hib hkeys).mp he] at hi
  exact Option.some.inj (hi.symm.trans hj)

private theorem packed_caption_key_not_node {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX ids inp o res)
    {key : Nat} {stored : Rect} (hmem : (key, stored) ∈ execution.packedAcc.titles)
    {source : ModelBox} (hsource : inp.boxes[key]? = some source) : source.role ≠ .node := by
  intro hrole
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨_, hpacked, _⟩ := bind_ok hpack
  obtain ⟨_, part, pos, original, _, hpart, hpos, htitle, _, _⟩ :=
    X_packedTitlesMemSource_closed ids execution hpacked hmem
  obtain ⟨candidate, run, loops, _, _, _, hplaced⟩ :=
    X_execution_part_run execution (List.mem_of_getElem? hpart)
  let cg := componentCandidate execution.graph part.1 candidate
  rw [hplaced] at htitle
  change (pos, original) ∈ (componentTitles execution.params cg run).map (fun q =>
    (q.1, shiftRect (0 - (placeBoundsX execution.params cg run execution.measured loops).minX)
      (-(placeBoundsX execution.params cg run execution.measured loops).minY) q.2)) at htitle
  obtain ⟨raw, hraw, hrawPos⟩ := List.mem_map.mp htitle
  obtain ⟨top, htop, hborder, htopPos, _, _⟩ :=
    componentTitles_dimension_source execution.params cg run hraw
  have hidx : top.2 = pos := htopPos.symm.trans (congrArg Prod.fst hrawPos)
  have hnode : cg.nodes[pos]? = some top.1 :=
    hidx ▸ List.mem_zipIdx_iff_getElem?.mp htop
  have hbound := sceneExecutionX_graph_len execution (List.getElem?_eq_some_iff.mp hsource).1
  have hbound0 : key < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact hbound
  have hgraph0 : execution.graph0.nodes[key]? = some execution.graph0.nodes[key] :=
    List.getElem?_eq_getElem hbound0
  obtain ⟨nd, hnd, hndBorder, _, _⟩ := exactGraph_node_key execution.graph_eq hgraph0
  have hcandidate : cg.nodes[pos]? = some nd := component_node_lookupX hpos hnd
  have hndTop : nd = top.1 := Option.some.inj (hcandidate.symm.trans hnode)
  apply measuredGraph_node_role_not_top execution.graph0_eq hsource hrole
  rw [List.getD_eq_getElem?_getD, hgraph0, Option.getD_some, ← hndBorder, hndTop]
  exact hborder

/-- Each live title in an exact leaf comes from an input group, not a node.
This uses the packed-part title origin and the executed border marker. -/
theorem exact_leaf_title_owner_group {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX ids inp o res)
    {title : String × Rect}
    (htitle : title ∈ sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc) :
    ∃ source ∈ inp.boxes, source.id = title.1 ∧ source.role = .group := by
  unfold sceneTitlesExpr at htitle
  obtain ⟨⟨k, rect⟩, hstored, hemit⟩ := List.mem_filterMap.mp htitle
  change (inp.boxes[k]?).bind (fun box =>
    let size := titleCaptionSize execution.params o (execution.lines.getD k [])
    some (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH { rect with w := size.w, h := size.h }))) =
    some title at hemit
  cases hbox : inp.boxes[k]? with
  | none => simp [hbox] at hemit
  | some box =>
    have hneq := packed_caption_key_not_node execution hstored hbox
    refine ⟨box, List.mem_of_getElem? hbox, ?_, ?_⟩
    · rw [hbox] at hemit
      exact congrArg Prod.fst (Option.some.inj hemit)
    · cases h : box.role with
      | node => exact (hneq h).elim
      | group => rfl

private def modelBoxKey (box : ModelBox) : String × String := (box.id, box.role.id)
private def sceneBoxKey (box : Box) : String × String := (box.id, box.role)

/-- Assembly data tied to either the flat scene or the actual recursive merge.
The line slots and box slots are both indexed by the original input. -/
structure CaptionSceneAssembly (inp : Input) (o : Options) (res : FamilyResult) where
  params : Params
  metric : Measure.Metric
  lines : List (List Measure.Line)
  titles : List (String × Rect)
  checked : checkedParams o.profile inp.kind = .ok params
  metric_ok : metricOf o.profile = .ok metric
  lines_ok : boxLines metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp = .ok lines
  box_keys : res.scene.boxes.map sceneBoxKey = inp.boxes.map modelBoxKey
  items_eq : res.scene.items = applyTitles titles
    (sceneItems params inp res.scene.boxes res.scene.routes lines res.scene.labels)
  title_owner : ∀ title ∈ titles, ∃ source ∈ inp.boxes,
    source.id = title.1 ∧ source.role = .group

/-- The indexed box lookup after assembly retains the model ID and role. -/
theorem CaptionSceneAssembly.box_at {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) {i : Nat} {source : ModelBox}
    (hsource : inp.boxes[i]? = some source) :
    ∃ placed, res.scene.boxes[i]? = some placed ∧
      placed.id = source.id ∧ placed.role = source.role.id := by
  have hkey := congrArg (fun keys : List (String × String) => keys[i]?) a.box_keys
  simp only [List.getElem?_map, hsource, Option.map_some] at hkey
  obtain ⟨placed, hplaced, he⟩ := Option.map_eq_some_iff.mp hkey
  exact ⟨placed, hplaced, congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- The installed title lookup never targets an admitted node, regardless of
whether the node has a validator label, or whether the measured text is empty. -/
theorem CaptionSceneAssembly.node_title_none {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) (hids : (inp.boxes.map (·.id)).Nodup)
    {source : ModelBox} (hsource : source ∈ inp.boxes) (hrole : source.role = .node) :
    a.titles.find? (fun title => title.1 == source.id) = none := by
  apply List.find?_eq_none.mpr
  intro title htitle hmatch
  obtain ⟨owner, howner, hid, hr⟩ := a.title_owner title htitle
  have he := same_key_of_nodup ModelBox.id hids howner hsource (hid.trans (beq_iff_eq.mp hmatch))
  rw [he, hrole] at hr
  cases hr

private theorem sceneItems_nonedge_origin {P : Params} {inp : Input} {boxes : List Box}
    {routes : List Route} {lines : List (List Measure.Line)} {labels : List SceneLabel}
    {raw : Group} (hraw : raw ∈ sceneItems P inp boxes routes lines labels)
    (hne : raw.role ≠ .edge) :
    ∃ box index, boxes[index]? = some box ∧ raw.owner = box.id ∧
      ((box.role = "group" ∧ raw = ⟨.group, box.id, groupItems P box.rect (lines.getD index [])⟩) ∨
       (box.role = "node" ∧ raw = ⟨.node, box.id, nodeItems P box.rect (lines.getD index [])⟩)) := by
  unfold sceneItems at hraw
  rcases List.mem_append.mp hraw with hframesOrEdges | hnodes
  · rcases List.mem_append.mp hframesOrEdges with hframes | hedges
    · obtain ⟨⟨box, i⟩, hpair, rfl⟩ := List.mem_map.mp hframes
      obtain ⟨hmem, hgroup⟩ := List.mem_filter.mp hpair
      exact ⟨box, i, List.mem_zipIdx_iff_getElem?.mp hmem, rfl, Or.inl ⟨beq_iff_eq.mp hgroup, rfl⟩⟩
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hedges
      exact (hne rfl).elim
  · obtain ⟨⟨box, i⟩, hpair, rfl⟩ := List.mem_map.mp hnodes
    obtain ⟨hmem, hnode⟩ := List.mem_filter.mp hpair
    exact ⟨box, i, List.mem_zipIdx_iff_getElem?.mp hmem, rfl, Or.inr ⟨beq_iff_eq.mp hnode, rfl⟩⟩

private theorem applyTitles_eq_of_no_title {titles : List (String × Rect)}
    {groups : List Group} {group : Group}
    (hnone : titles.find? (fun title => title.1 == group.owner) = none) :
    group ∈ applyTitles titles groups ↔ group ∈ groups := by
  let paint (raw : Group) : Group :=
    match titles.find? (fun title => title.1 == raw.owner) with
    | none => raw
    | some title => { raw with items := raw.items.map fun item =>
        match item with
        | .text t => .text { t with rect := title.2 }
        | _ => item }
  change group ∈ groups.map paint ↔ group ∈ groups
  constructor
  · intro h
    obtain ⟨raw, hraw, he⟩ := List.mem_map.mp h
    have hid : (paint raw).owner = raw.owner := by
      cases ht : titles.find? (fun title => title.1 == raw.owner) <;> simp [paint, ht]
    rw [he] at hid
    have hrawNone := hid ▸ hnone
    have heq : paint raw = raw := by simp only [paint, hrawNone]
    rw [← he, heq]
    exact hraw
  · intro h
    exact List.mem_map.mpr ⟨group, h, by simp only [paint, hnone]⟩

/-- The node caption is measured from the effective input text, including the
box-ID fallback when `Input.texts` has no slot for this declaration. -/
theorem CaptionSceneAssembly.caption_lines_at {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) {i : Nat} {source : ModelBox}
    (hsource : inp.boxes[i]? = some source) :
    StyledMeasure.wrap a.metric
      (Measure.wrapTarget a.metric.profile a.params.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD i source.id).toList = .ok (a.lines.getD i []) := by
  have hz : (inp.boxes.zipIdx)[i]? = some (source, i) := by
    simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add]
  have h := a.lines_ok
  unfold boxLines at h
  obtain ⟨ls, hw, hls⟩ := (mapM_getElem? _ _ _ h).2 i (source, i) hz
  simpa only [List.getD_eq_getElem?_getD, hls, Option.getD_some] using hw

/-- The unique non-edge item group is the literal `nodeItems` rebuild. Labels
never participate in this branch of `sceneItems`: multiple labels of the
same owner do not create extra primitives, and empty lines still give a text
primitive. -/
theorem CaptionSceneAssembly.node_normal_form {inp : Input} {o : Options} {res : FamilyResult}
    (a : CaptionSceneAssembly inp o res) (hids : (inp.boxes.map (·.id)).Nodup)
    {i : Nat} {source : ModelBox} (hsource : inp.boxes[i]? = some source)
    (hrole : source.role = .node) :
    ∃ placed, res.scene.boxes[i]? = some placed ∧ placed.id = source.id ∧ placed.role = "node" ∧
      let ls := a.lines.getD i []
      let canonical : Group := ⟨.node, source.id, nodeItems a.params placed.rect ls⟩
      canonical ∈ res.scene.items ∧
      (∀ other ∈ res.scene.items, other.role ≠ .edge → other.owner = source.id → other = canonical) ∧
      firstText canonical.items = some ⟨placed.rect.x,
        placed.rect.y + Int.tdiv (placed.rect.h - (ls.length : Int) * a.params.lineH) 2,
        placed.rect.w, (ls.length : Int) * a.params.lineH⟩ := by
  obtain ⟨placed, hplaced, hid, hrolePlaced⟩ := a.box_at hsource
  have hr : placed.role = "node" := by simpa only [hrole, BoxRole.id] using hrolePlaced
  let canonical : Group := ⟨.node, source.id, nodeItems a.params placed.rect (a.lines.getD i [])⟩
  have hnone := a.node_title_none hids (List.mem_of_getElem? hsource) hrole
  refine ⟨placed, hplaced, hid, hr, ?_, ?_, firstText_nodeItems _ _ _⟩
  · rw [a.items_eq]
    apply (applyTitles_eq_of_no_title (group := canonical) hnone).mpr
    unfold sceneItems
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(placed, i), List.mem_filter.mpr
      ⟨List.mem_zipIdx_iff_getElem?.mpr hplaced, by simp [hr]⟩, by simp [canonical, hid]⟩
  · intro other hother hne howner
    have hn : a.titles.find? (fun title => title.1 == other.owner) = none := by
      rw [howner]
      exact hnone
    rw [a.items_eq, applyTitles_eq_of_no_title hn] at hother
    obtain ⟨box, j, hj, hboxId, hshape⟩ := sceneItems_nonedge_origin hother hne
    have hkeys : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
      have hfst := congrArg (List.map (Prod.fst : String × String → String)) a.box_keys
      simp only [List.map_map] at hfst
      change res.scene.boxes.map Box.id = inp.boxes.map ModelBox.id at hfst
      exact hfst
    have hsame : box.id = placed.id := hboxId.symm.trans (howner.trans hid.symm)
    have hlookup : (res.scene.boxes.map (·.id))[i]? = (res.scene.boxes.map (·.id))[j]? := by
      simp only [List.getElem?_map, hplaced, hj, Option.map_some, hsame]
    have hib : i < (res.scene.boxes.map (·.id)).length := by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hplaced).1
    have hindex := (List.Nodup.getElem?_inj hib (by rwa [hkeys])).mp hlookup
    subst j
    have hsameBox : box = placed := Option.some.inj (hj.symm.trans hplaced)
    subst box
    rcases hshape with ⟨hgroup, _⟩ | ⟨_, he⟩
    · exact ((show ("node" : String) ≠ "group" from by decide) (hr.symm.trans hgroup)).elim
    · simpa only [canonical, hid] using he

/-- The exact leaf assembly uses the packed scene and the title table that was
actually passed to `applyTitles`. -/
def exactLeafCaptionAssembly {ids : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionX ids inp o res) : CaptionSceneAssembly inp o res where
  params := e.params
  metric := e.metric
  lines := e.lines
  titles := sceneTitlesExpr e.params inp o e.lines e.packedAcc
  checked := e.checked
  metric_ok := e.metric_eq
  lines_ok := e.lines_eq
  box_keys := by
    rw [e.boxes_eq_mapX, List.map_map]
    exact zipIdx_map_comp modelBoxKey inp.boxes 0
  items_eq := by rw [e.scene_eq]; rfl
  title_owner := fun _ ht => exact_leaf_title_owner_group e ht

private theorem selectInput_box_keys (inp : Input) (keep : ModelBox → Bool) (root : String) :
    (selectInput inp keep root).boxes.map modelBoxKey = (inp.boxes.filter keep).map modelBoxKey := by
  unfold selectInput
  dsimp only
  rw [List.map_map, ← zipIdx_filter_map_fst keep modelBoxKey inp.boxes 0]
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_apply]
  split <;> rfl

private theorem filterMap_eq_map_at_mem {α β : Type} {xs : List α}
    {f : α → Option β} {g : α → β} (h : ∀ x ∈ xs, f x = some (g x)) :
    xs.filterMap f = xs.map g := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filterMap_cons, h x List.mem_cons_self, List.map_cons, ht]

private theorem merge_box_keys {boxes : List ModelBox} {pool : List Box} {keep : ModelBox → Bool}
    (hids : (boxes.map (·.id)).Nodup)
    (hpool : pool.map sceneBoxKey =
      ((boxes.filter keep).map modelBoxKey) ++ ((boxes.filter fun b => !keep b).map modelBoxKey)) :
    (boxes.filterMap (fun model => pool.find? (fun box => box.id == model.id))).map sceneBoxKey =
      boxes.map modelBoxKey := by
  rw [List.map_filterMap]
  apply filterMap_eq_map_at_mem
  intro model hm
  have hmem : modelBoxKey model ∈ pool.map sceneBoxKey := by
    rw [hpool]
    cases h : keep model with
    | true => exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, h⟩))
    | false =>
      exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, by simp [h]⟩))
  change (pool.find? (fun box => box.id == model.id)).map sceneBoxKey = some (modelBoxKey model)
  cases hf : pool.find? (fun box => box.id == model.id) with
  | none =>
    obtain ⟨box, hb, hk⟩ := List.mem_map.mp hmem
    have hid : box.id = model.id := congrArg Prod.fst hk
    exact (List.find?_eq_none.mp hf box hb (beq_iff_eq.mpr hid)).elim
  | some box =>
    have hb : sceneBoxKey box ∈ pool.map sceneBoxKey :=
      List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
    rw [hpool, List.mem_append] at hb
    have hmodel : ∃ src ∈ boxes, modelBoxKey src = sceneBoxKey box := by
      rcases hb with hb | hb
      all_goals
        obtain ⟨src, hs, he⟩ := List.mem_map.mp hb
        exact ⟨src, (List.mem_filter.mp hs).1, he⟩
    obtain ⟨src, hs, he⟩ := hmodel
    have hid : box.id = model.id :=
      beq_iff_eq.mp (List.find?_some (p := fun box : Box => box.id == model.id) hf)
    have hid' : src.id = box.id := congrArg Prod.fst he
    have hsame := same_key_of_nodup ModelBox.id hids hs hm (hid'.trans hid)
    exact congrArg some (he.symm.trans (congrArg modelBoxKey hsame))

private theorem scene_groupTitle_owner {boxes : List ModelBox} {P : Params} {inp : Input}
    {s : Scene} {lines : List (List Measure.Line)} {titles : List (String × Rect)}
    (hkeys : s.boxes.map sceneBoxKey = boxes.map modelBoxKey)
    (hitems : s.items = applyTitles titles (sceneItems P inp s.boxes s.routes lines s.labels))
    {title : String × Rect} (htitle : title ∈ groupTitles s.items) :
    ∃ source ∈ boxes, source.id = title.1 ∧ source.role = .group := by
  obtain ⟨shown, hshown, hid, hrole, _⟩ := mem_groupTitles_iff.mp htitle
  rw [hitems] at hshown
  obtain ⟨raw, hraw, howner, hr, _⟩ := applyTitles_firstText_source hshown
  have hgroup : raw.role = .group := hr.symm.trans hrole
  obtain ⟨placed, _, hplaced, hplacedId, hshape⟩ := sceneItems_nonedge_origin hraw (by
    rw [hgroup]; decide)
  have hplacedRole : placed.role = "group" := by
    rcases hshape with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · rw [h] at hgroup
      cases hgroup
  have hmem : sceneBoxKey placed ∈ boxes.map modelBoxKey := by
    rw [← hkeys]
    exact List.mem_map_of_mem (List.mem_of_getElem? hplaced)
  obtain ⟨source, hsource, he⟩ := List.mem_map.mp hmem
  have hsRole : source.role.id = "group" := (congrArg Prod.snd he).trans hplacedRole
  exact ⟨source, hsource,
    (congrArg Prod.fst he).trans (hplacedId.symm.trans (howner.symm.trans hid)), by
      cases h : source.role with
      | node => simp [h, BoxRole.id] at hsRole
      | group => rfl⟩

/-- The exact recursive scene retains input box order and roles and installs
titles only for admitted group owners. This follows both recursive subcalls,
then the actual `expandChild` box merge, title table, and wrapping pass. -/
theorem exact_recursive_caption_assembly {ids : List String} (fuel : Nat)
    {inp : Input} {o : Options} {res : FamilyResult}
    (hids : (inp.boxes.map (·.id)).Nodup)
    (h : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) :
    Nonempty (CaptionSceneAssembly inp o res) := by
  induction fuel generalizing inp o res with
  | zero =>
    obtain ⟨e⟩ := layoutX_sceneExecution h
    exact ⟨exactLeafCaptionAssembly e⟩
  | succ fuel ih =>
    rcases layoutRecursiveB_succ_sources (layoutX ids) h with ⟨_, hl⟩ |
      ⟨group, P, _, child, titleLines, parent, hg, hP, _, hc, _, hp, hexpand⟩
    · obtain ⟨e⟩ := layoutX_sceneExecution hl
      exact ⟨exactLeafCaptionAssembly e⟩
    · let inside (box : ModelBox) := Compound.inside inp.boxes group.id box.id
      change layoutRecursiveB (layoutX ids) fuel (selectInput inp inside group.id)
        (childSubOptions o group) = .ok child at hc
      change layoutRecursiveB (layoutX ids) fuel (parentSubInput inp group P titleLines child) o =
        .ok parent at hp
      obtain ⟨ac⟩ := ih (selectInput_box_ids_nodup hids inside group.id) hc
      have hpids : ((parentSubInput inp group P titleLines child).boxes.map (·.id)).Nodup :=
        selectInput_box_ids_nodup hids (fun box => !inside box) ""
      obtain ⟨ap⟩ := ih hpids hp
      obtain ⟨frame, metric, tl, lines, dx, dy, _, hm, _, hl, _, _, hboxes, _, hitems⟩ :=
        expandChild_assembly_sources hexpand
      let embed (box : Box) : Box := { box with
        rect := shiftRect dx dy box.rect
        parent := if box.parent == "" then group.id else box.parent }
      let width := tl.foldl (fun w line => max w line.width) 0
      let height := (max 1 titleLines.length : Int) * P.lineH
      let rect := childTitleRect group.direction P.clusterPad width height frame.rect
      let titles := (group.id, rect) ::
        ((groupTitles child.scene.items).map (fun t => (t.1, shiftRect dx dy t.2)) ++
          groupTitles parent.scene.items)
      have hcKeys : child.scene.boxes.map sceneBoxKey =
          (inp.boxes.filter inside).map modelBoxKey := by
        rw [ac.box_keys, selectInput_box_keys]
      have hpKeys : parent.scene.boxes.map sceneBoxKey =
          (inp.boxes.filter (fun box => !inside box)).map modelBoxKey :=
        ap.box_keys.trans (selectInput_box_keys inp (fun box => !inside box) "")
      have hpool : (child.scene.boxes.map embed ++ parent.scene.boxes).map sceneBoxKey =
          (inp.boxes.filter inside).map modelBoxKey ++
            (inp.boxes.filter (fun box => !inside box)).map modelBoxKey := by
        rw [List.map_append, List.map_map]
        change child.scene.boxes.map sceneBoxKey ++ parent.scene.boxes.map sceneBoxKey = _
        rw [hcKeys, hpKeys]
      refine ⟨⟨P, metric, lines, titles, hP, hm, hl, ?_, hitems, ?_⟩⟩
      · rw [hboxes]
        exact merge_box_keys hids hpool
      · intro title htitle
        rcases List.mem_cons.mp htitle with rfl | ht
        · have hselected := List.find?_some (p := fun box : ModelBox =>
            Compound.independent inp.boxes inp.routes box &&
              !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) hg
          have hind := (Bool.and_eq_true_iff.mp hselected).1
          simp only [Compound.independent, Bool.and_eq_true, beq_iff_eq] at hind
          exact ⟨group, List.mem_of_find?_eq_some hg, rfl, hind.1.1⟩
        · rcases List.mem_append.mp ht with hct | hpt
          · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hct
            obtain ⟨src, hs, hid, hr⟩ := scene_groupTitle_owner hcKeys ac.items_eq hold
            exact ⟨src, (List.mem_filter.mp hs).1, hid, hr⟩
          · obtain ⟨src, hs, hid, hr⟩ := scene_groupTitle_owner hpKeys ap.items_eq hpt
            exact ⟨src, (List.mem_filter.mp hs).1, hid, hr⟩

/-- Caption assembly for the exact family execution used by the public adapter,
before attachment projection and `drawShapes`. -/
theorem usecase_executed_caption_assembly {m : Model} {fixed : List (String × Size)}
    {res : FamilyResult}
    (h : layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
      (input m fixed) m.options = .ok res) :
    Nonempty (CaptionSceneAssembly (input m fixed) m.options res) := by
  obtain ⟨hwf, hrec⟩ := layoutFamilyB_success h
  change layoutRecursiveB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
    (m.boxes.length + 1) (input m fixed) m.options = .ok res at hrec
  unfold layoutRecursiveX at hrec
  rw [layoutRecursiveB_compose] at hrec
  exact exact_recursive_caption_assembly _ (Model.boxIds_nodup hwf) hrec

/-- Unlike full fixed-size admission, this node-only invariant survives the
recursive insertion of fixed sizes for nonexclusive group frames. -/
def NonexclusiveNodesUnfixed (inp : Input) : Prop :=
  ∀ source ∈ inp.boxes, source.role = .node → source.exclusive = false →
    inp.fixedSizes.any (fun entry => entry.1 == source.id) = false

theorem admitted_nonexclusive_nodes_unfixed {inp : Input}
    (hadm : layeredAdmissibleB inp = true) : NonexclusiveNodesUnfixed inp := by
  intro source hsource _ hex
  simp only [layeredAdmissibleB, Bool.and_eq_true] at hadm
  have hadmFixed := hadm.1.2
  change inp.fixedSizes.all
    (fun entry => inp.boxes.all (fun box => box.id != entry.1 || box.exclusive)) = true at hadmFixed
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨entry, hentry, hid⟩ := List.any_eq_true.mp h
  have he := List.all_eq_true.mp (List.all_eq_true.mp hadmFixed entry hentry) source hsource
  simp [beq_iff_eq.mp hid, hex] at he

theorem NonexclusiveNodesUnfixed.select {inp : Input} (h : NonexclusiveNodesUnfixed inp)
    (keep : ModelBox → Bool) (root : String) :
    NonexclusiveNodesUnfixed (selectInput inp keep root) := by
  intro box hb hr hex
  obtain ⟨source, hs, _, he⟩ := selectInput_box_source inp keep root box hb
  have hid : box.id = source.id := by rw [he]; split <;> rfl
  have hrole : box.role = source.role := by rw [he]; split <;> rfl
  have hexcl : box.exclusive = source.exclusive := by rw [he]; split <;> rfl
  change inp.fixedSizes.any (fun entry => entry.1 == box.id) = false
  rw [hid]
  exact h source hs (hrole.symm.trans hr) (hexcl.symm.trans hex)

theorem NonexclusiveNodesUnfixed.parent {inp : Input} (h : NonexclusiveNodesUnfixed inp)
    (hids : (inp.boxes.map (·.id)).Nodup) {group : ModelBox} (hg : group ∈ inp.boxes)
    (hrole : group.role = .group) (P : Params) (titleLines : List Measure.Line)
    (child : FamilyResult) :
    NonexclusiveNodesUnfixed (parentSubInput inp group P titleLines child) := by
  let keep (box : ModelBox) := !Compound.inside inp.boxes group.id box.id
  intro box hb hr hex
  change box ∈ (selectInput inp keep "").boxes at hb
  obtain ⟨source, hs, _, he⟩ := selectInput_box_source inp keep "" box hb
  have hid : box.id = source.id := by rw [he]; split <;> rfl
  have hr' : source.role = .node := by
    rw [he] at hr
    split at hr <;> exact hr
  have hkey : group.id ≠ box.id := by
    intro hh
    have heq := same_key_of_nodup ModelBox.id hids hg hs (hh.trans hid)
    rw [heq, hr'] at hrole
    cases hrole
  have hnone := h.select keep "" box hb hr hex
  change ((selectInput inp keep "").fixedSizes ++ [(group.id, _)]).any
    (fun entry => entry.1 == box.id) = false
  simp [List.any_append, hnone, hkey]

/-- A nonexclusive node in a reachable exact leaf uses the same rectangle for
its fallback scene label and its display text. The unfixed node has enough
height for the two integer division conventions to agree. -/
theorem exact_leaf_unfixed_node_caption_rect {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (e : SceneExecutionX ids inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup) (hunfixed : NonexclusiveNodesUnfixed inp)
    {i : Nat} {source : ModelBox} (hsource : inp.boxes[i]? = some source)
    (hrole : source.role = .node) (hex : source.exclusive = false) :
    ∃ placed, res.scene.boxes[i]? = some placed ∧
      firstText (nodeItems e.params placed.rect (e.lines.getD i [])) =
        some (sceneCaptionRect e.params inp o e.lines e.packedAcc i source.id) := by
  let a := exactLeafCaptionAssembly e
  obtain ⟨placed, hplaced, _, hplacedRole⟩ := a.box_at hsource
  have hr : placed.role = "node" := by simpa only [hrole, BoxRole.id] using hplacedRole
  have hmem := List.mem_of_getElem? hsource
  have hnone := a.node_title_none hids hmem hrole
  change (sceneTitlesExpr e.params inp o e.lines e.packedAcc).find?
    (fun title => title.1 == source.id) = none at hnone
  have hz : (inp.boxes.zipIdx)[i]? = some (source, i) := by
    simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add]
  have hl := e.lines_eq
  unfold boxLines at hl
  obtain ⟨ls, _, hls⟩ := (mapM_getElem? _ _ _ hl).2 i (source, i) hz
  have hfit := ((xctb_ordinaryBoxLineHeightX_holds ids) e hplaced hsource hrole
    (hunfixed source hmem hrole hex) hls).2
  have hslack : 0 ≤ placed.rect.h - (ls.length : Int) * e.params.lineH := by omega
  have hdiv : Int.tdiv (placed.rect.h - (ls.length : Int) * e.params.lineH) 2 =
      Int.fdiv (placed.rect.h - (ls.length : Int) * e.params.lineH) 2 := by
    rw [Int.tdiv_eq_ediv_of_nonneg hslack, Int.fdiv_eq_ediv_of_nonneg _ (b := 2) (by decide)]
  have hb : res.scene.boxes = sceneBoxesExpr e.params inp o e.packedAcc := e.boxes_eq_mapX
  refine ⟨placed, hplaced, ?_⟩
  rw [firstText_nodeItems, sceneCaptionRect, hnone, ← hb]
  simp only [List.getD_eq_getElem?_getD, hplaced, hls, Option.map_none, Option.getD_none,
    Option.getD_some, ownedTextRect, hr, show ("node" == "group") = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hdiv]

end Elegant.Kinds.Usecase
