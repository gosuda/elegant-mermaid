import Elegant.Kinds.UsecaseDrawShapesProof
import Elegant.Kinds.UsecaseValidExact

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

open Layered Layered.PipelineImpl

private theorem filterMapM_member_ok {α β : Type} (f : α → Except LayoutError (Option β)) :
    ∀ (xs : List α) (ys : List β), xs.filterMapM f = .ok ys →
      ∀ x ∈ xs, ∃ found, f x = .ok found ∧ ∀ y, found = some y → y ∈ ys := by
  intro xs
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro ys h x hx
    rw [List.filterMapM_cons] at h
    obtain ⟨found, hfound, h⟩ := bind_ok' h
    cases found with
    | none =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨none, hfound, fun _ he => by cases he⟩
      · exact ih ys h x hx
    | some value =>
      obtain ⟨tail, htail, h⟩ := bind_ok' h
      have he : value :: tail = ys := Except.ok.inj h
      subst ys
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨some value, hfound, fun y hy => ?_⟩
        rw [← Option.some.inj hy]
        exact List.mem_cons_self
      · obtain ⟨found, hxFound, hmem⟩ := ih tail htail x hx
        exact ⟨found, hxFound, fun y hy => List.mem_cons_of_mem _ (hmem y hy)⟩

private theorem actor_nodeSize_ok {p : Profile} {shape text : String}
    {out : Option (Size × Bool)} (ha : isActor shape = true)
    (h : nodeSize p shape text = .ok out) : ∃ size, out = some (size, true) := by
  have hs : isSized shape = true := by simp [isSized, ha]
  cases p <;>
    simp only [nodeSize, hs, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, actorMetrics] at h <;>
    obtain ⟨_, _, h⟩ := bind_ok' h <;>
    obtain ⟨_, _, h⟩ := bind_ok' h <;>
    obtain ⟨_, _, h⟩ := bind_ok' h <;>
    obtain ⟨w, _, h⟩ := bind_ok' h <;>
    obtain ⟨ht, _, h⟩ := bind_ok' h <;>
    exact ⟨⟨w, ht⟩, (Except.ok.inj h).symm⟩

private theorem actor_mem_sizes {m : Model} {fixed : List (String × Size)}
    (h : sizes m = .ok fixed) {b : ModelBox} (hb : b ∈ m.boxes)
    (ha : isActor b.shape = true) : ∃ s, (b.id, s) ∈ fixed := by
  unfold sizes at h
  obtain ⟨found, hfound, hmem⟩ := filterMapM_member_ok _ _ _ h b hb
  obtain ⟨out, hout, h⟩ := bind_ok' hfound
  obtain ⟨sz, rfl⟩ := actor_nodeSize_ok ha hout
  exact ⟨sz, hmem _ (Except.ok.inj h).symm⟩

private theorem admitted_actor_exclusive {m : Model} {fixed : List (String × Size)}
    (hadm : Layered.layeredAdmissibleB (input m fixed) = true)
    (hfixed : sizes m = .ok fixed) {b : ModelBox} (hb : b ∈ m.boxes)
    (ha : isActor b.shape = true) : b.exclusive = true := by
  obtain ⟨s, hs⟩ := actor_mem_sizes hfixed hb ha
  simp only [Layered.layeredAdmissibleB, Bool.and_eq_true] at hadm
  have h := hadm.1.2
  change fixed.all (fun e => m.boxes.all (fun x => (x.id != e.1 || x.exclusive))) = true at h
  have he := List.all_eq_true.mp h (b.id, s) hs
  simpa using List.all_eq_true.mp he b hb

private structure SuppressedOwner (inp : Input) (owner : String) : Prop where
  notRoute : owner ∉ inp.routes.map (·.id)
  exclusive : ∀ b ∈ inp.boxes, b.id = owner → b.exclusive = true
  boxed : ∀ l ∈ inp.labels, l.owner = owner → owner ∈ inp.boxes.map (·.id)

private theorem SuppressedOwner.select {inp : Input} {owner : String}
    (h : SuppressedOwner inp owner) (keep : ModelBox → Bool) (root : String) :
    SuppressedOwner (selectInput inp keep root) owner := by
  have hn : owner ∉ (selectInput inp keep root).routes.map (·.id) :=
    fun hm => h.notRoute ((selectInput_routes_ids_sublist inp keep root).subset hm)
  refine ⟨hn, ?_, ?_⟩
  · intro b hb howner
    obtain ⟨orig, horig, _, hselect⟩ := selectInput_box_source inp keep root b hb
    have hid : b.id = orig.id := by rw [hselect]; split <;> rfl
    have hex : b.exclusive = orig.exclusive := by rw [hselect]; split <;> rfl
    exact hex.trans (h.exclusive orig horig (hid.symm.trans howner))
  · intro l hl howner
    rcases selectInput_label_owner inp keep root l hl with hbox | hroute
    · exact howner ▸ hbox
    · exact (hn (howner ▸ hroute)).elim

private theorem SuppressedOwner.fixedTables {inp : Input} {owner : String}
    (h : SuppressedOwner inp owner) (sizes : List (String × Size))
    (children : List (String × Scene)) (areas : List (String × Int)) :
    SuppressedOwner { inp with fixedSizes := sizes, fixedChildren := children, fixedAreas := areas }
      owner := ⟨h.notRoute, h.exclusive, h.boxed⟩

private theorem flat_suppresses_owner {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult} {owner : String}
    (h : layoutX ids inp o = .ok res) (hs : SuppressedOwner inp owner) :
    ∀ l ∈ res.scene.labels, l.owner ≠ owner := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  intro l hl howner
  rw [execution.scene_eq] at hl
  simp only [sceneOf] at hl
  obtain ⟨⟨src, index⟩, hsrc, hlabel⟩ := List.mem_filterMap.mp hl
  have hsame : l.owner = src.owner := by
    split at hlabel
    · contradiction
    · split at hlabel
      · have hlOwner := congrArg (fun label : SceneLabel => label.toLabel.owner)
          (Option.some.inj hlabel)
        exact hlOwner.symm
      · split at hlabel
        · contradiction
        · have hlOwner := congrArg (fun label : SceneLabel => label.toLabel.owner)
            (Option.some.inj hlabel)
          exact hlOwner.symm
  have hsrcOwner : src.owner = owner := hsame.symm.trans howner
  have hsrcMem : src ∈ inp.labels := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hsrc)
  obtain ⟨b, hb, hid⟩ := List.mem_map.mp (hs.boxed src hsrcMem hsrcOwner)
  have hex := hs.exclusive b hb hid
  have hblocked : inp.boxes.any (fun box => box.id == src.owner && box.exclusive) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp [hid, hsrcOwner, hex]⟩
  simp [hblocked] at hlabel

private theorem expanded_label_owner {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {height : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group height parent child = .ok res) {l : SceneLabel}
    (hl : l ∈ res.scene.labels) :
    ∃ src ∈ child.scene.labels ++ parent.scene.labels, src.owner = l.owner := by
  obtain ⟨frame, metric, title, _, dx, dy, hf, hm, ht, _, hx, hy, _, _⟩ := expandChild_sources h
  rw [expandChild_labels_eq_wrapped h frame title dx dy hf hx hy ⟨metric, hm, ht⟩] at hl
  obtain ⟨model, _, hlabel⟩ := List.mem_filterMap.mp hl
  cases hfind : (((child.scene.labels.map fun label : SceneLabel =>
      { label with rect := shiftRect dx dy label.rect }) ++ parent.scene.labels).find?
      (fun label : SceneLabel => label.id == model.id)) with
  | none => simp [hfind] at hlabel
  | some picked =>
    rw [hfind, Option.bind_some] at hlabel
    have he := Option.some.inj hlabel
    have howner : picked.owner = l.owner := by
      split at he
      all_goals
        have hlOwner := congrArg (fun label : SceneLabel => label.toLabel.owner) he
        exact hlOwner
    rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hchild | hparent
    · obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hchild
      exact ⟨src, List.mem_append_left _ hsrc, howner⟩
    · exact ⟨picked, List.mem_append_right _ hparent, howner⟩

private theorem recursive_suppresses_owner (ids : List String) (owner : String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursiveB (layoutX ids) fuel inp o = .ok res → SuppressedOwner inp owner →
      ∀ l ∈ res.scene.labels, l.owner ≠ owner := by
  intro fuel
  induction fuel with
  | zero => intro inp o res h hs; exact flat_suppresses_owner h hs
  | succ fuel ih =>
    intro inp o res h hs l hl howner
    rcases layoutRecursiveB_succ_sources (layoutX ids) h with ⟨_, hflat⟩ |
      ⟨group, _, _, child, _, parent, _, _, _, hchild, _, hparent, hexpand⟩
    · exact flat_suppresses_owner hflat hs l hl howner
    · obtain ⟨src, hsrc, hsOwner⟩ := expanded_label_owner hexpand hl
      rcases List.mem_append.mp hsrc with hc | hp
      · exact ih _ _ _ hchild (hs.select _ _) src hc (hsOwner.trans howner)
      · exact ih _ _ _ hparent ((hs.select _ _).fixedTables _ _ _) src hp (hsOwner.trans howner)

/-- Actor captions are redrawn as primitives, but admission and family label emission
prevent any actor-owned validator label on the actual run. -/
theorem executed_actor_owns_no_label {m : Model} {fixed : List (String × Size)}
    {res : FamilyResult} (hadm : Layered.layeredAdmissibleB (input m fixed) = true)
    (hwf : WellFormed m) (hfixed : sizes m = .ok fixed)
    (hrun : Layered.layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
      (input m fixed) m.options = .ok res)
    {b : ModelBox} (hb : b ∈ m.boxes) (ha : isActor b.shape = true) :
    ∀ l ∈ res.scene.labels, l.owner ≠ b.id := by
  have hmem : b.id ∈ (input m fixed).boxes.map (·.id) := List.mem_map.mpr ⟨b, hb, rfl⟩
  have hs : SuppressedOwner (input m fixed) b.id := by
    refine ⟨Layered.layeredAdmissibleB_disjoint hadm b.id hmem, ?_, fun _ _ _ => hmem⟩
    intro other hother hid
    have hn := Model.boxIds_nodup hwf
    have hleft := Assembly.keyed_lookup_eq ModelBox.id m.boxes hn other hother
    have hright := Assembly.keyed_lookup_eq ModelBox.id m.boxes hn b hb
    rw [hid] at hleft
    have he := Option.some.inj (hleft.symm.trans hright)
    rw [he]
    exact admitted_actor_exclusive hadm hfixed hb ha
  have hrec := (Layered.layoutFamilyB_success hrun).2
  change layoutRecursiveB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
    (m.boxes.length + 1) (input m fixed) m.options = .ok res at hrec
  unfold layoutRecursiveX at hrec
  rw [layoutRecursiveB_compose] at hrec
  exact recursive_suppresses_owner _ _ _ _ _ _ hrec hs

/-- For a validator label in the redrawn result, a `MovedBy` witness can only
copy the first input text rectangle. The actor-caption transform is unreachable
in this branch, regardless of the model's kind. -/
theorem executed_movedLabel_firstText {m : Model} {fixed : List (String × Size)}
    {res : FamilyResult} {proj drawn : Scene}
    (hadm : Layered.layeredAdmissibleB (input m fixed) = true)
    (hwf : WellFormed m) (hfixed : sizes m = .ok fixed)
    (hrun : Layered.layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
      (input m fixed) m.options = .ok res)
    (hproj : res.scene.projectCellAttachments (Common.routeMarkers m) = proj)
    (hdraw : drawShapes m proj = .ok drawn)
    {l : SceneLabel} (hl : l ∈ drawn.labels) {g : Group}
    (hmoved : MovedBy m proj g l.owner l.rect) : firstText g.items = some l.rect := by
  obtain ⟨src, hsrc, _, hsame, _, _, _⟩ := drawShapes_labels_spec hdraw l hl
  have hlabels : proj.labels = res.scene.labels := by
    rw [← hproj]
    unfold Scene.projectCellAttachments
    split <;> rfl
  rw [hlabels] at hsrc
  obtain ⟨box, placed, hbox, _, howner, rect, hrect, heq⟩ := hmoved
  have hboxId : box.id = g.owner := by
    have hmatch := List.find?_some (p := fun b : ModelBox => b.id == g.owner) hbox
    exact beq_iff_eq.mp hmatch
  have hActor : isActor box.shape = false := by
    cases ha : isActor box.shape with
    | false => rfl
    | true =>
      exfalso
      exact (executed_actor_owns_no_label hadm hwf hfixed hrun
        (List.mem_of_find?_eq_some hbox) ha src hsrc)
        (hsame.symm.trans (howner.symm.trans hboxId.symm))
  rw [heq]
  simpa [movedItems, hActor] using hrect

/-- The box-derived label rectangle in the executed flat scene is also the first
text rectangle in its display group. Both read the same installed title; in the
node fallback branch the executed size fit makes the two divisions agree.
Agreement with the original validator-label rectangle after recursive
`expandChild` remains open. -/
theorem exact_leaf_caption_firstText {ids : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX ids inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfit : InputFixedFit inp o)
    {key : Nat} {source : ModelBox} (hsrc : inp.boxes[key]? = some source)
    (hex : source.exclusive = false)
    (howned : ∃ label ∈ inp.labels, label.owner = source.id) :
    ∃ g ∈ res.scene.items, g.owner = source.id ∧ g.role ≠ .edge ∧
      firstText g.items = some (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc key source.id) := by
  let P := execution.params
  let ls := execution.lines.getD key []
  let titles := sceneTitlesExpr P inp o execution.lines execution.packedAcc
  let box : Box := ⟨source.id, source.role.id,
    shiftRect P.canvasMargin P.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD key default)), source.parent, source.exclusive⟩
  have hb : res.scene.boxes[key]? = some box := by
    rw [execution.boxes_eq_mapX]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsrc, Option.map_some, Nat.zero_add] <;> rfl
  have hbox : (sceneBoxesExpr P inp o execution.packedAcc).getD key
      ⟨"", "", default, "", false⟩ = box := by
    have hbeq : res.scene.boxes = sceneBoxesExpr P inp o execution.packedAcc :=
      execution.boxes_eq_mapX
    rw [← hbeq, List.getD_eq_getElem?_getD, hb] <;> rfl
  have hz : (box, key) ∈ res.scene.boxes.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hb
  let raw : Group := match source.role with
    | .group => ⟨.group, source.id, groupItems P box.rect ls⟩
    | .node => ⟨.node, source.id, nodeItems P box.rect ls⟩
  have hraw : raw ∈ sceneItems P inp res.scene.boxes res.scene.routes execution.lines
      res.scene.labels := by
    unfold sceneItems
    cases hr : source.role with
    | group =>
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨(box, key), List.mem_filter.mpr ⟨hz, by simp [box, hr, BoxRole.id]⟩,
        by simp [raw, hr, ls, box]⟩
    | node =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨(box, key), List.mem_filter.mpr ⟨hz, by simp [box, hr, BoxRole.id]⟩,
        by simp [raw, hr, ls, box]⟩
  let present : Group := match titles.find? (fun title => title.1 == raw.owner) with
    | none => raw
    | some title => { raw with items := raw.items.map fun primitive =>
        match primitive with
        | .text text => .text { text with rect := title.2 }
        | _ => primitive }
  have hfields := straightenAcc_fields execution.straight_eq
  have hitems : res.scene.items = applyTitles titles
      (sceneItems P inp res.scene.boxes res.scene.routes execution.lines res.scene.labels) := by
    rw [execution.scene_eq]
    simp only [sceneOf, hfields.2.2.1, hfields.2.2.2.2] <;> rfl
  refine ⟨present, ?_, ?_⟩
  · rw [hitems]
    exact List.mem_map.mpr ⟨raw, hraw, rfl⟩
  have hid : raw.owner = source.id := by cases hr : source.role <;> simp [raw, hr]
  cases ht : titles.find? (fun title => title.1 == source.id) with
  | some title =>
    have htitle : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun t => t.1 == source.id) = some title := ht
    cases hr : source.role <;>
      simp [present, ht, raw, hr, groupItems, nodeItems, firstText, sceneCaptionRect, htitle]
  | none =>
    have htitle : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun t => t.1 == source.id) = none := ht
    have hcaption : sceneCaptionRect execution.params inp o execution.lines execution.packedAcc
        key source.id = ownedTextRect P box ls := by
      unfold sceneCaptionRect
      rw [htitle]
      change ownedTextRect P ((sceneBoxesExpr P inp o execution.packedAcc).getD key
        ⟨"", "", default, "", false⟩) ls = ownedTextRect P box ls
      rw [hbox]
    cases hr : source.role with
    | group =>
      simp [present, ht, raw, hr, groupItems, firstText, hcaption, ownedTextRect, box,
        BoxRole.id]
    | node =>
      have hcontain := xctb_ownerCaptionContainFallbackFitW_of_cases ids
        (X_FallbackOwnerCasesX_holds ids (X_NonfixedGroupTitleX_holds ids))
        inp o res execution hwf hfit key source hsrc htitle hex howned
      rw [hbox] at hcontain
      have hrole : box.role = "node" := by simp [box, hr, BoxRole.id]
      have hheight : 0 ≤ box.rect.h - (ls.length : Int) * P.lineH := by
        change box.rect.Contained (ownedTextRect P box ls) at hcontain
        have hgroup : ¬ (box.role == "group") = true := by simp [hrole]
        rw [ownedTextRect, ite_eq_right hgroup] at hcontain
        have htop : box.rect.y ≤
            box.rect.y + Int.fdiv (box.rect.h - (ls.length : Int) * P.lineH) 2 :=
          hcontain.2.2.1
        rw [Int.fdiv_eq_ediv_of_nonneg _ (b := 2) (by decide)] at htop
        apply (Int.ediv_nonneg_iff_of_pos (show (0 : Int) < 2 by decide)).mp
        apply Int.le_of_add_le_add_left (a := box.rect.y)
        simpa only [Int.add_zero] using htop
      have hdivision : Int.tdiv (box.rect.h - (ls.length : Int) * P.lineH) 2 =
          Int.fdiv (box.rect.h - (ls.length : Int) * P.lineH) 2 := by
        rw [Int.tdiv_eq_ediv_of_nonneg hheight, Int.fdiv_eq_ediv_of_nonneg _ (b := 2) (by decide)]
      simp [present, ht, raw, hr, nodeItems, firstText, hcaption, ownedTextRect, hrole,
        hdivision]

/-- A projected display group that does not represent a route retains all of
its primitives and can be traced directly to the family scene. -/
theorem project_nonedge_group_source {s : Scene} {markers : List RouteMarkers}
    {g : Group} (hg : g ∈ (s.projectCellAttachments markers).items) (hrole : g.role ≠ .edge) :
    g ∈ s.items := by
  by_cases hp : s.profile = .cell
  · rw [Scene.projectCellAttachments_items s markers hp] at hg
    obtain ⟨orig, hmem, rfl⟩ := List.mem_map.mp hg
    cases orig with
    | mk role owner items =>
      cases role
      case edge => exact (hrole rfl).elim
      all_goals
        change (⟨_, owner, items.zipIdx.map (fun q => q.1)⟩ : Group) ∈ s.items
        rw [zipIdx_map_fst]
        exact hmem
  · rw [Scene.projectCellAttachments_vector s markers hp] at hg
    exact hg

private theorem edge_item_route {P : Params} {inp : Input} {boxes : List Box}
    {routes : List Route} {lines : List (List Measure.Line)} {labels : List SceneLabel}
    {titles : List (String × Rect)} {g : Group}
    (hg : g ∈ applyTitles titles (sceneItems P inp boxes routes lines labels))
    (hrole : g.role = .edge) : ∃ r ∈ routes, r.id = g.owner := by
  unfold applyTitles at hg
  obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hg
  have hfields : raw.role = g.role ∧ raw.owner = g.owner := by
    cases ht : titles.find? (fun title => title.1 == raw.owner) <;> simp only [ht] at heq
    all_goals
      subst g
      exact ⟨rfl, rfl⟩
  have hr : raw.role = .edge := hfields.1.trans hrole
  unfold sceneItems at hraw
  rcases List.mem_append.mp hraw with hframesOrEdges | hnodes
  · rcases List.mem_append.mp hframesOrEdges with hframes | hedges
    · obtain ⟨q, _, heq⟩ := List.mem_map.mp hframes
      rw [← heq] at hr
      contradiction
    · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hedges
      have hqelem := List.mem_zipIdx_iff_getElem?.mp hq
      exact ⟨q.1, List.mem_of_getElem? hqelem,
        (congrArg Group.owner heq).trans hfields.2⟩
  · obtain ⟨q, _, heq⟩ := List.mem_map.mp hnodes
    rw [← heq] at hr
    contradiction

private theorem flat_edge_item_owner {ids : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX ids inp o = .ok res) {g : Group}
    (hg : g ∈ res.scene.items) (hrole : g.role = .edge) :
    g.owner ∈ inp.routes.map (·.id) := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  rw [execution.scene_eq] at hg
  obtain ⟨r, hr, hid⟩ := edge_item_route hg hrole
  change r ∈ inp.routes.zipIdx.map _ at hr
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hr
  have he : q.1.id = r.id := congrArg Route.id heq
  exact List.mem_map.mpr
    ⟨q.1, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hq), he.trans hid⟩

private theorem recursive_edge_item_owner {ids : List String} {inp : Input} {o : Options}
    {res : FamilyResult} {fuel : Nat}
    (h : layoutRecursiveB (layoutX ids) fuel inp o = .ok res) {g : Group}
    (hg : g ∈ res.scene.items) (hrole : g.role = .edge) :
    g.owner ∈ inp.routes.map (·.id) := by
  cases fuel with
  | zero => exact flat_edge_item_owner h hg hrole
  | succ fuel =>
    rcases layoutRecursiveB_succ_sources (layoutX ids) h with ⟨_, hflat⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hexpand⟩
    · exact flat_edge_item_owner hflat hg hrole
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hroutes, hitems⟩ :=
        expandChild_assembly_sources hexpand
      rw [hitems] at hg
      obtain ⟨r, hr, hid⟩ := edge_item_route hg hrole
      rw [hroutes] at hr
      obtain ⟨source, hsource, hfind⟩ := List.mem_filterMap.mp hr
      have hmatch := List.find?_some (p := fun route : Route => route.id == source.id) hfind
      have hsourceId : r.id = source.id := beq_iff_eq.mp hmatch
      exact List.mem_map.mpr ⟨source, hsource, hsourceId.symm.trans hid⟩

private theorem projected_group_owner {s : Scene} {markers : List RouteMarkers} {g : Group}
    (hg : g ∈ (s.projectCellAttachments markers).items) :
    ∃ original ∈ s.items, original.owner = g.owner ∧ original.role = g.role := by
  by_cases hp : s.profile = .cell
  · rw [Scene.projectCellAttachments_items s markers hp] at hg
    obtain ⟨orig, hmem, rfl⟩ := List.mem_map.mp hg
    exact ⟨orig, hmem, rfl, rfl⟩
  · rw [Scene.projectCellAttachments_vector s markers hp] at hg
    exact ⟨g, hg, rfl, rfl⟩

/-- The redraw's moved-label witness refers to a box display group in the
original exact-family result, with precisely its original first text. -/
theorem executed_movedLabel_source {m : Model} {fixed : List (String × Size)}
    {res : FamilyResult} {proj drawn : Scene}
    (hadm : Layered.layeredAdmissibleB (input m fixed) = true)
    (hwf : WellFormed m) (hfixed : sizes m = .ok fixed)
    (hrun : Layered.layoutFamilyB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
      (input m fixed) m.options = .ok res)
    (hproj : res.scene.projectCellAttachments (Common.routeMarkers m) = proj)
    (hdraw : drawShapes m proj = .ok drawn)
    {l : SceneLabel} (hl : l ∈ drawn.labels) {g : Group} (hg : g ∈ proj.items)
    (hmoved : MovedBy m proj g l.owner l.rect) :
    g ∈ res.scene.items ∧ firstText g.items = some l.rect := by
  refine ⟨?_, executed_movedLabel_firstText hadm hwf hfixed hrun hproj hdraw hl hmoved⟩
  rw [← hproj] at hg
  apply project_nonedge_group_source hg
  intro hedge
  obtain ⟨original, horig, howner, hrole⟩ := projected_group_owner hg
  have hrec := (Layered.layoutFamilyB_success hrun).2
  change layoutRecursiveB (layoutRecursiveX (actorIds m) (m.boxes.length + 1))
    (m.boxes.length + 1) (input m fixed) m.options = .ok res at hrec
  unfold layoutRecursiveX at hrec
  rw [layoutRecursiveB_compose] at hrec
  have hr := recursive_edge_item_owner hrec horig (hrole.trans hedge)
  obtain ⟨box, _, hbox, _⟩ := hmoved
  have hmatch := List.find?_some (p := fun b : ModelBox => b.id == g.owner) hbox
  have hboxId : box.id = g.owner := beq_iff_eq.mp hmatch
  have hmBox : original.owner ∈ (input m fixed).boxes.map (·.id) :=
    List.mem_map.mpr ⟨box, List.mem_of_find?_eq_some hbox, hboxId.trans howner.symm⟩
  exact Layered.layeredAdmissibleB_disjoint hadm original.owner hmBox hr

end Elegant.Kinds.Usecase
