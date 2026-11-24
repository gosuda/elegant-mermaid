import Elegant.Layered.RegionActiveOwnCaption
import Elegant.Layered.RegionFallbackAncestorSelectedStrict

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem r8b_sceneBoxAt {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {src : ModelBox} (hsrc : inp.boxes[key]? = some src) :
    ∃ b : Box, res.scene.boxes[key]? = some b ∧ b.id = src.id ∧ b.parent = src.parent ∧
      b.role = src.role.id ∧
      b.rect = shiftRect e.params.canvasMargin e.params.canvasMargin
        (orientRect o.direction e.packedAcc.canvasH (e.packedAcc.rects.getD key default)) := by
  let b : Box := ⟨src.id, src.role.id, shiftRect e.params.canvasMargin e.params.canvasMargin
    (orientRect o.direction e.packedAcc.canvasH (e.packedAcc.rects.getD key default)),
    src.parent, src.exclusive⟩
  refine ⟨b, ?_, rfl, rfl, rfl, rfl⟩
  rw [e.boxes_eq_mapR]
  simp only [List.getElem?_map, List.getElem?_zipIdx, hsrc, Option.map_some, Nat.zero_add, b]

/-- A source declaration on the measured path of another declaration occurs in the
emitted dump's parent walk. The walk starts from the emitted owner, not its parent. -/
theorem sceneExecutionR_sourceAncestor_of_path {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {ownerKey key : Nat} {owner src : ModelBox}
    (howner : inp.boxes[ownerKey]? = some owner) (hsrc : inp.boxes[key]? = some src)
    (hpath : key ∈ Compound.path inp.boxes owner) :
    src.id ∈ res.scene.layoutDump.ancestors owner.id := by
  let dump := res.scene.layoutDump
  have hids : dump.boxes.map (·.id) = inp.boxes.map (·.id) := by
    change res.scene.boxes.map (·.id) = inp.boxes.map (·.id)
    rw [e.boxes_eq_mapR, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hnodup : (dump.boxes.map (·.id)).Nodup := by
    rw [hids]
    exact Model.boxIds_nodup hwf
  have hlookup {j : Nat} {b : ModelBox} (hb : inp.boxes[j]? = some b) :
      ∃ emitted, dump.box? b.id = some emitted ∧ emitted.parent = b.parent := by
    obtain ⟨emitted, hemitted, hid, hparent, _, _⟩ := r8b_sceneBoxAt e hb
    have hfind : dump.box? emitted.id = some emitted :=
      Assembly.keyed_lookup_eq Box.id dump.boxes hnodup emitted (List.mem_of_getElem? hemitted)
    exact ⟨emitted, by simpa only [hid] using hfind, hparent⟩
  have hwalk : ∀ (fuel j : Nat) (b : ModelBox), inp.boxes[j]? = some b →
      key ∈ Compound.ancestors inp.boxes fuel b.parent →
      src.id ∈ LayoutDump.ancestors.go dump fuel b.id := by
    intro fuel
    induction fuel with
    | zero =>
      intro j b hb hmem
      simp [Compound.ancestors] at hmem
    | succ fuel ih =>
      intro j b hb hmem
      by_cases hroot : b.parent = ""
      · simp [hroot, Compound.ancestors] at hmem
      cases hfind : inp.boxes.findIdx? (fun p => p.id == b.parent) with
      | none => simp [Compound.ancestors, hfind] at hmem
      | some k =>
        obtain ⟨hk, hid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
        let parent := inp.boxes[k]
        have hkGet : inp.boxes[k]? = some parent := List.getElem?_eq_getElem hk
        have hpid : parent.id = b.parent := beq_iff_eq.mp hid
        have hm : key ∈ Compound.ancestors inp.boxes fuel parent.parent ++ [k] := by
          simpa only [Compound.ancestors, hfind, hkGet] using hmem
        obtain ⟨emitted, hemitted, hemittedParent⟩ := hlookup hb
        have hstep : LayoutDump.ancestors.go dump (fuel + 1) b.id =
            b.parent :: LayoutDump.ancestors.go dump fuel b.parent := by
          simp only [LayoutDump.ancestors.go, hemitted, hemittedParent, hroot, ↓reduceIte]
        rw [hstep]
        apply List.mem_cons.mpr
        rcases List.mem_append.mp hm with htail | hhere
        · exact Or.inr (by simpa only [hpid] using ih k parent hkGet htail)
        · have he := List.mem_singleton.mp hhere
          have hAtParent : inp.boxes[key]? = some parent := by rwa [he]
          have hsame : src = parent := Option.some.inj (hsrc.symm.trans hAtParent)
          exact Or.inl ((congrArg ModelBox.id hsame).trans hpid)
  have hlen : dump.boxes.length = inp.boxes.length := by
    simpa only [List.length_map] using congrArg List.length hids
  change src.id ∈ LayoutDump.ancestors.go dump dump.boxes.length owner.id
  rw [hlen]
  exact hwalk inp.boxes.length ownerKey owner howner hpath

private theorem r8b_projectedStrictInside_inv (d : Direction) (height dx dy margin : Int)
    {frame inner : Rect}
    (h : (shiftRect margin margin (orientRect d height (shiftRect dx dy frame))).StrictInside
      (shiftRect margin margin (orientRect d height (shiftRect dx dy inner)))) :
    frame.StrictInside inner := by
  cases d <;> simp only [Rect.StrictInside, shiftRect, orientRect] at h ⊢ <;> omega

/-- Strict frame ancestry holds in the stored coordinates of the same executed part.
Both stored rectangles travel through the same shelf, orientation, and canvas margin. -/
theorem r8b_partSourceAncestor_strictInside {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) {part : List Nat × Part}
    (hpart : part ∈ e.componentsAcc.parts) {i pos ownerKey key : Nat} {owner src : ModelBox}
    {ownFrame frame : Rect}
    (hownKey : part.1[i]? = some ownerKey) (hkey : part.1[pos]? = some key)
    (howner : inp.boxes[ownerKey]? = some owner) (hsrc : inp.boxes[key]? = some src)
    (hgroup : src.role = .group) (hpath : key ∈ Compound.path inp.boxes owner)
    (hownFrame : part.2.rects[i]? = some ownFrame) (hframe : part.2.rects[pos]? = some frame) :
    frame.StrictInside ownFrame := by
  have hp := e.packed_eq
  unfold packAcc at hp
  obtain ⟨packed, hpacked, _⟩ := bind_ok hp
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpart
  have hclen : c < packed.boxes.length := by
    rw [Pack.pack_count hpacked, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hc).1
  let shelf := packed.boxes[c]
  have hshelf : packed.boxes[c]? = some shelf := List.getElem?_eq_getElem hclen
  have hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some (part, shelf) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hshelf⟩
  have hpackedAt {atPos decl : Nat} {source : ModelBox} {rect : Rect}
      (hdecl : part.1[atPos]? = some decl) (hsource : inp.boxes[decl]? = some source)
      (hrect : part.2.rects[atPos]? = some rect) :
      e.packedAcc.rects.getD decl default = shiftRect shelf.x shelf.y rect := by
    have hentry : (part.1.zip part.2.rects)[atPos]? = some (decl, rect) :=
      List.getElem?_zip_eq_some.mpr ⟨hdecl, hrect⟩
    have hsize : decl < e.componentsAcc.rects.size := by
      rw [e.components_rects_sizeR]
      exact (List.getElem?_eq_some_iff.mp hsource).1
    exact actual_components_packed_rect_valueR (by rfl) e.components_eq e.packed_eq packed
      hpacked hselected hentry hsize default
  obtain ⟨a, ha, haId, _, haRole, haRect⟩ := r8b_sceneBoxAt e hsrc
  obtain ⟨b, hb, hbId, _, _, hbRect⟩ := r8b_sceneBoxAt e howner
  have hrole : a.role = "group" := by simp only [haRole, hgroup, BoxRole.id]
  have hancestor : a.id ∈ res.scene.layoutDump.ancestors b.id := by
    rw [haId, hbId]
    exact sceneExecutionR_sourceAncestor_of_path e hwf howner hsrc hpath
  have hstrict := R_ancestorFrameStrictW_closed exactIds idSets e hwf hfp a b
    (List.mem_of_getElem? ha) (List.mem_of_getElem? hb) hrole hancestor
  rw [haRect, hbRect, hpackedAt hkey hsrc hframe, hpackedAt hownKey howner hownFrame] at hstrict
  exact r8b_projectedStrictInside_inv o.direction e.packedAcc.canvasH shelf.x shelf.y
    e.params.canvasMargin hstrict

/-- An active title's selected group marker records the target group declaration as
an ancestor, excluding the marker's own declaration at the end of its path. -/
def R8b_ActiveAncestorCaption {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (i pos : Nat) : Prop :=
  ∃ (s : RegionSpec) (owner target : Node), selected.spec = some s ∧
    selected.cg.nodes[i]? = some owner ∧ owner.border = -2 ∧
    selected.cg.nodes[pos]? = some target ∧ target.border = -2 ∧
    owner.decl ≠ target.decl ∧ target.decl ∈ owner.clusterPath

/-- The measured active caption lies strictly inside its selected ancestor frame,
in the same part-local coordinates as the C8b caption check. -/
theorem r8b_activeAncestorCaption_strictInside {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {e : SceneExecutionR exactIds idSets inp o res} {part : List Nat × Part}
    (selected : R8b_ChosenPart e part) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hpart : part ∈ e.componentsAcc.parts)
    {i pos key : Nat} {src : ModelBox} {stored frame : Rect}
    (hmem : (i, stored) ∈ part.2.titles) (hkey : part.1[pos]? = some key)
    (hsrc : inp.boxes[key]? = some src) (hgroup : src.role = .group)
    (hframe : part.2.rects[pos]? = some frame) (hancestor : R8b_ActiveAncestorCaption selected i pos) :
    let size := titleCaptionSize e.params o (e.lines.getD (part.1.getD i 0) [])
    frame.StrictInside { stored with w := size.w, h := size.h } := by
  obtain ⟨s, owner, target, hs, ho, hoTop, ht, htTop, hne, hmemPath⟩ := hancestor
  have hcomp : part.1 ∈ components e.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) e.components_eq).1]
    exact List.mem_map_of_mem hpart
  have hrun := selected.run_eq
  rw [hs] at hrun
  have hresolved : newComponentRegions selected.spec e.params inp
      (componentCandidateR selected.spec e.graph part.1 selected.candidate) =
        .ok selected.regions := by
    rw [selected.effective_eq]
    exact componentTrialR_selected_regions _ selected.regions_eq
  obtain ⟨rm, hrm⟩ : ∃ rm, selected.regions = some rm := by
    cases h : selected.regions with
    | none =>
      have he := selected.effective_eq
      rw [hs, h] at he
      cases he
    | some rm => exact ⟨rm, rfl⟩
  rw [hs, hrm] at hresolved
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hresolved
  have hnodes : selected.cg.nodes =
      (componentCandidateR (some s) e.graph part.1 selected.candidate).nodes :=
    rankEquivalentR_nodes_eq hrank
  have hoCandidate := ho
  have htCandidate := ht
  rw [hnodes] at hoCandidate htCandidate
  have hoKey := (active_candidate_top_source e hcomp hoCandidate hoTop).1
  have htKey := (active_candidate_top_source e hcomp htCandidate htTop).1
  have htarget : key = target.decl := Option.some.inj (hkey.symm.trans htKey)
  have hoExact : (componentCandidate e.graph part.1 selected.candidate).nodes[i]? = some owner := by
    rw [componentCandidate_nodes]
    exact hoCandidate
  obtain ⟨ownerSource, hownerSource, hpath⟩ :=
    X_cg_group_box e.graph0_eq e.graph_eq hoExact hoTop
  have hsourcePath : key ∈ Compound.path inp.boxes ownerSource := by
    rw [htarget]
    rw [hpath, List.mem_append, List.mem_singleton] at hmemPath
    exact hmemPath.resolve_right (Ne.symm hne)
  have hrectLen : part.2.rects.length = selected.cg.nodes.length := by
    rw [selected.part_eq]
    simp [placeComponentExact]
  have hi : i < part.2.rects.length := by
    rw [hrectLen]
    exact (List.getElem?_eq_some_iff.mp ho).1
  let ownFrame := part.2.rects[i]
  have hownFrame : part.2.rects[i]? = some ownFrame := List.getElem?_eq_getElem hi
  have houter := r8b_partSourceAncestor_strictInside e hwf hfp hpart hoKey hkey hownerSource
    hsrc hgroup hsourcePath hownFrame hframe
  exact captionStrictInside_trans houter
    (r8b_activeOwnCaption_strictInside selected hpart hs hmem hownFrame)

/-- The active-caption remainder with strictly ancestral group frames removed.
The existing route and caption exclusions are unchanged. -/
def R_ExecutedPartFrameCoresB8ActiveAncestorCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ part ∈ execution.componentsAcc.parts,
      (∀ (selected : R8b_ChosenPart execution part)
        (index : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (index, stored) ∈ part.2.labels → part.1[pos]? = some key →
        inp.boxes[key]? = some src → src.role = .group → part.2.rects[pos]? = some frame →
        ¬ R8b_EmittedOuterReversedAt selected index stored pos →
        ¬ R8b_EmittedReservedChildAt selected index pos →
        ¬ R8b_EmittedDemotedReversedAt selected index stored pos src →
        ¬ R8b_EmittedSelectedLoopFrameAt selected index pos →
        ¬ R8b_EmittedForwardChildAt selected index pos →
        Disjoint frame stored ∨ frame.StrictInside stored) ∧
      (∀ (selected : R8b_ChosenPart execution part)
        (i : Nat) (stored : Rect) (pos key : Nat) (src : ModelBox) (frame : Rect),
        (i, stored) ∈ part.2.titles → part.1[pos]? = some key →
        inp.boxes[key]? = some src → src.role = .group → part.2.rects[pos]? = some frame →
        ¬ R8b_ActiveForeignCaption selected i pos →
        ¬ (i = pos ∧ ∃ s, selected.spec = some s) →
        ¬ R8b_ActiveAncestorCaption selected i pos →
        let size := titleCaptionSize execution.params o (execution.lines.getD (part.1.getD i 0) [])
        Disjoint frame { stored with w := size.w, h := size.h } ∨
          frame.StrictInside { stored with w := size.w, h := size.h })

theorem R_activeCaptionRemainder_iff_activeAncestorCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ExecutedPartFrameCoresB8ActiveCaptionRemainder exactIds idSets ↔
      R_ExecutedPartFrameCoresB8ActiveAncestorCaptionRemainder exactIds idSets := by
  classical
  constructor
  · intro h inp o res e hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h e hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro selected i stored pos key src frame hm hk hs hg hf hforeign hown _
    exact hcaption selected i stored pos key src frame hm hk hs hg hf hforeign hown
  · intro h inp o res e hwf hfp part hpart
    obtain ⟨hroute, hcaption⟩ := h e hwf hfp part hpart
    refine ⟨hroute, ?_⟩
    intro selected i stored pos key src frame hm hk hs hg hf hforeign hown
    by_cases hancestor : R8b_ActiveAncestorCaption selected i pos
    · exact Or.inr (r8b_activeAncestorCaption_strictInside selected hwf hfp hpart hm hk hs hg hf
        hancestor)
    · exact hcaption selected i stored pos key src frame hm hk hs hg hf hforeign hown hancestor

theorem flatC8bB_layoutRIds_activeAncestorCaptionRemainder (exactIds : List String)
    (idSets : List (String × List String))
    (hcores : R_ExecutedPartFrameCoresB8ActiveAncestorCaptionRemainder exactIds idSets)
    (hfallW : R_FallbackCaptionClearBW exactIds idSets)
    (hres : R_PartSizingRResidual exactIds idSets)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (layoutRIds exactIds idSets) :=
  flatC8bB_layoutRIds_activeCaptionRemainder exactIds idSets
    ((R_activeCaptionRemainder_iff_activeAncestorCaptionRemainder exactIds idSets).mpr hcores)
    hfallW hres hcap

end Elegant.Layered.PipelineImpl
