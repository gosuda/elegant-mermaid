import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RegionNotesCrossBundleC8a
import Elegant.Layered.RegionSharedAllocation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem bundleTargetOrigin (boxes : List ModelBox) (atts : List Attach) :
    ∀ b ∈ bundlesOf boxes atts,
      (∃ a ∈ atts, a.target = b.target) ∧ isNested boxes atts b.target = false := by
  unfold bundlesOf
  refine List.foldlRecOn (motive := fun bs : List Bundle => ∀ b ∈ bs,
    (∃ a ∈ atts, a.target = b.target) ∧ isNested boxes atts b.target = false) atts _ ?_ ?_
  · simp
  · intro acc ih next hnext
    by_cases h : (isNested boxes atts next.target || acc.any (·.target == next.target)) = true
    · simpa only [ite_eq_left h] using ih
    · simp only [ite_eq_right h]
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ih b hb
      · obtain rfl := List.mem_singleton.mp hb
        refine ⟨⟨next, hnext, rfl⟩, ?_⟩
        cases hn : isNested boxes atts next.target with
        | false => rfl
        | true => simp [hn] at h

theorem noteBundleTargets_not_ancestor {boxes : List ModelBox} {atts : List Attach}
    {a b : Bundle} (ha : a ∈ bundlesOf boxes atts) (hb : b ∈ bundlesOf boxes atts)
    {top : ModelBox} (htop : boxes[b.target]? = some top) :
    a.target ∉ Compound.path boxes top := by
  obtain ⟨src, hsrc, ht⟩ := (bundleTargetOrigin boxes atts a ha).1
  have hn := (bundleTargetOrigin boxes atts b hb).2
  simp only [isNested, htop] at hn
  intro hm
  have htrue : (Compound.path boxes top).any (fun i => atts.any (·.target == i)) = true :=
    List.any_eq_true.mpr ⟨a.target, hm, List.any_eq_true.mpr ⟨src, hsrc, beq_iff_eq.mpr ht⟩⟩
  rw [hn] at htrue
  cases htrue

private theorem executedBundleOrigin
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    l.bundle ∈ e.bundles ∧ inp.boxes[l.bundle.target]? = some l.top := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨hlen, hget⟩ := mapM_getElem? _ _ _ e.layouts_eq
  have hib : i < e.bundles.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨out, hrun, hout⟩ := hget i e.bundles[i] (List.getElem?_eq_getElem hib)
  have he := Option.some.inj (hout.symm.trans hi)
  subst out
  unfold bundleLayout at hrun
  cases ht : inp.boxes[e.bundles[i].target]? with
  | none => simp [ht] at hrun
  | some top =>
    simp only [ht] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    have he := Except.ok.inj hrun
    have hb : e.bundles[i] = l.bundle := congrArg BundleLayout.bundle he
    have htop : top = l.top := congrArg BundleLayout.top he
    rw [← hb, ← htop]
    exact ⟨List.getElem_mem hib, ht⟩

theorem executedNoteBundleTops_not_ancestor
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {a b : BundleLayout} (ha : a ∈ e.layouts) (hb : b ∈ e.layouts) :
    a.bundle.target ∉ Compound.path inp.boxes b.top ∧
    b.bundle.target ∉ Compound.path inp.boxes a.top := by
  obtain ⟨ha, hta⟩ := executedBundleOrigin e ha
  obtain ⟨hb, htb⟩ := executedBundleOrigin e hb
  rw [e.bundles_eq, e.atts_eq] at ha hb
  exact ⟨noteBundleTargets_not_ancestor ha hb htb, noteBundleTargets_not_ancestor hb ha hta⟩

private theorem sourcePlainBox {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (ex : SceneExecutionR exactIds idSets inp o res) {b : Box}
    (hb : b ∈ res.scene.boxes) (hrole : b.role ≠ "group") :
    ∃ (key : Nat) (source : ModelBox) (node : Node),
      inp.boxes[key]? = some source ∧ b.id = source.id ∧
      ex.graph.nodes[key]? = some node ∧ node.border = 0 ∧
      b.rect = shiftRect ex.params.canvasMargin ex.params.canvasMargin
        (orientRect o.direction ex.packedAcc.canvasH (ex.packedAcc.rects.getD key default)) := by
  rw [ex.boxes_eq_mapR] at hb
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hb
  have hsrc := List.mem_zipIdx_iff_getElem?.mp hentry
  have hkey : entry.2 < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsrc).1
  have hlineBound : entry.2 < ex.lines.length := by
    rw [boxLines_length ex.lines_eq]
    exact hkey
  obtain ⟨node0, hn0, hb0⟩ := measuredGraph_exclusive_node_border_zero ex.checked
    ex.graph0_eq (List.getElem?_eq_getElem hlineBound) hsrc
    (fun hg => hrole (by simp [hg, BoxRole.id]))
  obtain ⟨node, hn, hborder, _, _⟩ := exactGraph_node_key ex.graph_eq hn0
  exact ⟨entry.2, entry.1, node, hsrc, rfl, hn, hborder.trans hb0, rfl⟩

private theorem selectedPackedFrames {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (ex : SceneExecutionR exactIds idSets inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      ex.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (ex.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part} (hk : ex.componentsAcc.parts[k]? = some part)
    (hkLen : k < packed.boxes.length) :
    ∃ selected : R8a_SelectedPartRun ex part,
      ∀ {pos key : Nat}, part.1[pos]? = some key → key < inp.boxes.length →
        let bounds := placeBoundsX ex.params selected.cg selected.run ex.measured selected.loops
        let r := shiftRect packed.boxes[k].x packed.boxes[k].y
          (shiftRect (0 - bounds.minX) (-bounds.minY)
            (frameRect ex.params selected.cg selected.run pos))
        packed.boxes[k].Contained r ∧ ex.packedAcc.rects.getD key default = r := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR hempty ex.components_eq
  obtain ⟨candidate, chosen, cg, run, loops, area, spec, hcand, hportfolio, hwinner,
    ⟨regions, hregions, heffective⟩, hrun, hloops, hpart⟩ := hall part (List.mem_of_getElem? hk)
  let selected : R8a_SelectedPartRun ex part :=
    ⟨candidate, chosen, spec, regions, cg, run, loops, area, hcand, hportfolio, hwinner,
      hregions, heffective, hrun, hloops, hpart⟩
  refine ⟨selected, ?_⟩
  intro pos key hpos hkey
  dsimp only
  let bounds := placeBoundsX ex.params cg run ex.measured loops
  let r := shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect ex.params cg run pos)
  change packed.boxes[k].Contained (shiftRect packed.boxes[k].x packed.boxes[k].y r) ∧
    ex.packedAcc.rects.getD key default = shiftRect packed.boxes[k].x packed.boxes[k].y r
  have hlen : (componentCandidateR spec ex.graph part.1 candidate).nodes.length = part.1.length := by
    cases spec with
    | none =>
      rw [componentCandidateR_none, componentCandidate_nodes]
      exact List.length_map ..
    | some _ =>
      unfold componentCandidateR componentGraph
      dsimp only
      exact List.length_map ..
  have hposLen : pos < cg.nodes.length := by
    rw [componentRunR_nodes_eq hrun, hlen]
    exact (List.getElem?_eq_some_iff.mp hpos).1
  have hframe : (placeComponentExact ex.params cg run 0 ex.measured loops).rects[pos]? = some r := by
    unfold r bounds placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hposLen, Option.map_some]
  have hpartRect : part.2.rects[pos]? = some r := by
    rw [hpart]
    exact hframe
  have hkMap : k < (ex.componentsAcc.parts.map
      (fun p => Pack.Item.mk p.2.width p.2.height p.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  have hdim := congrArg (fun l => l[k]?) (Pack.pack_dimensions hpack)
  unfold Pack.dimensions at hdim
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hkLen,
    List.getElem?_eq_getElem hkMap] at hdim
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdim
  rw [List.getElem_map, (List.getElem?_eq_some_iff.mp hk).2] at hdim
  change packed.boxes[k].w = part.2.width ∧ packed.boxes[k].h = part.2.height at hdim
  constructor
  · have hbound := placeComponentExact_rects_bounds ex.params cg run 0 ex.measured loops r
      (List.mem_of_getElem? hframe)
    simp only [Rect.Contained, shiftRect] at hbound ⊢
    have hw := congrArg Part.width hpart
    have hh := congrArg Part.height hpart
    dsimp only at hw hh
    rw [hdim.1, hdim.2, hw, hh]
    omega
  · have hshelf : (ex.componentsAcc.parts.zip packed.boxes)[k]? = some (part, packed.boxes[k]) :=
      List.getElem?_zip_eq_some.mpr ⟨hk, List.getElem?_eq_getElem hkLen⟩
    have hsize : key < ex.componentsAcc.rects.size := by
      rw [ex.components_rects_sizeR]
      exact hkey
    have hentry : (part.1.zip part.2.rects)[pos]? = some (key, r) :=
      List.getElem?_zip_eq_some.mpr ⟨hpos, hpartRect⟩
    exact actual_components_packed_rect_valueR hempty ex.components_eq ex.packed_eq packed hpack
      hshelf hentry hsize default

private theorem selectedPlainFramesDisjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (ex : SceneExecutionR exactIds idSets inp o res) {part : List Nat × Part}
    (selected : R8a_SelectedPartRun ex part) (hcomp : part.1 ∈ components ex.graph)
    {a b ka kb : Nat} {an bn : Node}
    (ha : part.1[a]? = some ka) (hb : part.1[b]? = some kb)
    (hna : ex.graph.nodes[ka]? = some an) (hnb : ex.graph.nodes[kb]? = some bn)
    (hba : an.border = 0) (hbb : bn.border = 0) (hne : a ≠ b) :
    Disjoint (frameRect ex.params selected.cg selected.run a)
      (frameRect ex.params selected.cg selected.run b) := by
  have hnodes : selected.cg.nodes =
      (componentCandidateR selected.spec ex.graph part.1 selected.candidate).nodes := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ :=
      componentRunR_stages selected.run_eq
    rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hrank⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq hrank
  have hca : selected.cg.nodes[a]? = some an := by
    rw [hnodes]
    exact component_node_lookupR ha hna
  have hcb : selected.cg.nodes[b]? = some bn := by
    rw [hnodes]
    exact component_node_lookupR hb hnb
  have hrun := selected.run_eq
  cases hs : selected.spec with
  | none =>
    rw [hs] at hrun
    exact componentRunR_positions_disjointR_none ex.graph0_eq ex.graph_eq hcomp hrun
      hca hcb hba hbb hne
  | some s =>
    rw [hs] at hrun
    by_cases hr : (rk selected.run.proper.rank a).toNat = (rk selected.run.proper.rank b).toNat
    · have hactive : newComponentRegions selected.spec ex.params inp
          (componentCandidateR selected.spec ex.graph part.1 selected.candidate) =
          .ok selected.regions := by
        rw [selected.effective_eq]
        exact componentTrialR_selected_regions (g := ex.graph) (comp := part.1)
          selected.candidate selected.regions_eq
      rw [hs] at hactive
      cases hreg : selected.regions with
      | none =>
        have he := selected.effective_eq
        rw [hs, hreg] at he
        simp at he
      | some rm =>
        rw [hreg] at hactive
        have hgap := componentRunR_active_plain_same_rank_gap ex.checked hrun hactive
          hca hcb hba hbb hne hr
        unfold R8a_OverlapRowsXGap at hgap
        unfold Disjoint Rect.meetsInterior
        rintro ⟨hx, hy⟩
        have hxGap := hgap hy (by omega) (by omega)
        omega
    · exact componentRunR_positions_disjointR_different_rank hrun hca hcb hba hbb hr

/-- Plain boxes are disjoint in the actual selected and packed region execution. -/
theorem executedRegionPlainBoxes_disjoint {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (ex : SceneExecutionR exactIds idSets inp o res) {a b : Box}
    (ha : a ∈ res.scene.boxes) (hb : b ∈ res.scene.boxes) (hne : a.id ≠ b.id)
    (hpa : a.role ≠ "group") (hpb : b.role ≠ "group") : Disjoint a.rect b.rect := by
  obtain ⟨ka, sa, na, hsa, hida, hna, hba, hra⟩ := sourcePlainBox ex ha hpa
  obtain ⟨kb, sb, nb, hsb, hidb, hnb, hbb, hrb⟩ := sourcePlainBox ex hb hpb
  have hka := (List.getElem?_eq_some_iff.mp hsa).1
  have hkb := (List.getElem?_eq_some_iff.mp hsb).1
  have hkeys : ka ≠ kb := by
    intro h
    rw [h] at hsa
    exact hne (hida.trans ((congrArg ModelBox.id (Option.some.inj (hsa.symm.trans hsb))).trans hidb.symm))
  obtain ⟨pa, ia, ca, hpaMem, hca, hia⟩ := key_part_positionR ex hka
  obtain ⟨pb, ib, cb, _, hcb, hib⟩ := key_part_positionR ex hkb
  have hpacked := ex.packed_eq
  unfold packAcc at hpacked
  obtain ⟨packed, hpack, -⟩ := bind_ok hpacked
  have hShelf {k : Nat} {part : List Nat × Part} (hk : ex.componentsAcc.parts[k]? = some part) :
      k < packed.boxes.length := by
    rw [Pack.pack_count hpack, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  rw [hra, hrb]
  apply not_meetsInterior_shiftRect
  apply not_meetsInterior_orientRect
  by_cases hsame : ca = cb
  · subst cb
    have he := Option.some.inj (hca.symm.trans hcb)
    subst pb
    obtain ⟨selected, hframes⟩ := selectedPackedFrames ex packed hpack hca (hShelf hca)
    have hcomp : pa.1 ∈ components ex.graph := by
      rw [← (actual_components_parts_geometryR (by rfl) ex.components_eq).1]
      exact List.mem_map.mpr ⟨pa, hpaMem, rfl⟩
    have hpos : ia ≠ ib := by
      intro heq
      rw [heq] at hia
      exact hkeys (Option.some.inj (hia.symm.trans hib))
    have hraw := selectedPlainFramesDisjoint ex selected hcomp hia hib hna hnb hba hbb hpos
    rw [(hframes hia hka).2, (hframes hib hkb).2]
    exact not_meetsInterior_shiftRect (not_meetsInterior_shiftRect hraw)
  · obtain ⟨_, hframesA⟩ := selectedPackedFrames ex packed hpack hca (hShelf hca)
    obtain ⟨_, hframesB⟩ := selectedPackedFrames ex packed hpack hcb (hShelf hcb)
    obtain ⟨hfitA, hstoreA⟩ := hframesA hia hka
    obtain ⟨hfitB, hstoreB⟩ := hframesB hib hkb
    rw [hstoreA, hstoreB]
    exact disjoint_of_contained_disjoint hfitA hfitB
      (Pack.pack_boxes_disjoint hpack ca cb (hShelf hca) (hShelf hcb) hsame)

private abbrev noteRegionBase (idSets : List (String × List String)) :=
  fun (ids : List String) (inp : Input) (o : Options) =>
    layoutRIds ids (reindexRegionSets idSets inp) inp o

/-- All different-parent envelopes are separated; no contracted C2/C3/C8a premise is needed. -/
theorem regionNotes_differentParentEnvelopes_disjoint {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (noteRegionBase idSets) exactIds fuel inp o res) :
    NotesC8aEnvDisjExceptSiblings e := by
  intro a ha b hb hne ea eb hea heb _
  have hida : ea.id = a.top.id := beq_iff_eq.mp
    (List.find?_some (p := fun x : Box => x.id == a.top.id) (a := ea)
      (show e.contracted.scene.boxes.find? (fun x : Box => x.id == a.top.id) = some ea from hea))
  have hidb : eb.id = b.top.id := beq_iff_eq.mp
    (List.find?_some (p := fun x : Box => x.id == b.top.id) (a := eb)
      (show e.contracted.scene.boxes.find? (fun x : Box => x.id == b.top.id) = some eb from heb))
  obtain ⟨ex⟩ := layoutRIds_sceneExecution e.contracted_eq
  have hd := executedRegionPlainBoxes_disjoint ex (List.mem_of_find?_eq_some hea)
    (List.mem_of_find?_eq_some heb) (by simpa only [hida, hidb] using hne)
    (by rw [regionNotes_envelope_role_node (idSets := idSets) e ha hea]; decide)
    (by rw [regionNotes_envelope_role_node (idSets := idSets) e hb heb]; decide)
  simpa only [envRect, hea, heb] using hd

/-- A placed fragment clears every unclaimed non-group box of the contracted execution. -/
theorem mixedNotesC8aClear_keptNonGroup {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (noteRegionBase idSets) exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) {p : Placed}
    (hp : p ∈ placedOf' e.margin e.contracted.scene l) {sb cb : Box}
    (hsb : sb ∈ p.scene.boxes) (hcb : cb ∈ e.contracted.scene.boxes)
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r)
    (hrole : cb.role ≠ "group") :
    Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect := by
  obtain ⟨env, henv⟩ := regionNotes_envelope_exists (idSets := idSets) e hl
  have henvId : env.id = l.top.id := beq_iff_eq.mp
    (List.find?_some (p := fun b : Box => b.id == l.top.id) henv)
  have hne : env.id ≠ cb.id := by
    rw [henvId]
    exact regionNotes_unclaimed_ne_bundleTop (idSets := idSets) e hl hfree
  obtain ⟨ex⟩ := layoutRIds_sceneExecution e.contracted_eq
  have hd := executedRegionPlainBoxes_disjoint ex (List.mem_of_find?_eq_some henv) hcb hne
    (by rw [regionNotes_envelope_role_node (idSets := idSets) e hl henv]; decide) hrole
  have hfit := regionNotes_envelope_contains (idSets := idSets) e l hl p hp sb hsb
  rw [envRect, henv] at hfit
  exact Disjoint.of_contained_left hfit hd

/-- The remaining mixed case pairs a non-part fragment with an unclaimed input group. -/
def NotesC8aClearKeptGroupOutsidePart
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∀ cb ∈ e.contracted.scene.boxes,
      (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
      sb.id ≠ cb.id →
      sb.id ∉ (inpDumpOf inp).ancestors cb.id →
      cb.id ∉ (inpDumpOf inp).ancestors sb.id →
      (∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group") →
      p.scene ≠ l.part.scene →
      Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect

theorem notesC8aClearExceptPartKeptGroup_of_keptGroupOutsidePart
    {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (noteRegionBase idSets) exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hremain : NotesC8aClearKeptGroupOutsidePart e) : NotesC8aClearExceptPartKeptGroup e := by
  intro l hl p hp sb hsb cb hcb hfree hne hanc hforeign _ hnotPartKept
  by_cases hgroup : cb.role = "group"
  · obtain ⟨ib, hib, hid, hrole⟩ := regionNotes_unclaimed_source_role (idSets := idSets)
      e hwf hcb hfree
    have hsource : ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group" :=
      ⟨ib, hib, hid, hrole.trans hgroup⟩
    exact hremain l hl p hp sb hsb cb hcb hfree hne hanc hforeign hsource
      (fun hpart => hnotPartKept ⟨hpart, hsource⟩)
  · exact mixedNotesC8aClear_keptNonGroup (idSets := idSets) e hl hp hsb hcb hfree hgroup

theorem regionNotes_c8aGeomT_of_mixedResidual {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (noteRegionBase idSets) exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hmixed : NotesC8aClearKeptGroupOutsidePart e)
    (hcontract : Validator.C8a e.contracted.scene.layoutDump) :
    NotesC8aGeomT e := by
  have hEnv := regionNotes_envelope_contains (idSets := idSets) e
  have hEnvDisj := notesC8aEnvDisj_of_exceptSiblings (idSets := idSets) e
    (regionNotes_differentParentEnvelopes_disjoint (idSets := idSets) e)
  have hRemaining := notesC8aClearExceptPartKeptGroup_of_keptGroupOutsidePart
    (idSets := idSets) e hwf hmixed
  have hClear := notesC8aClear_of_exceptPartKeptGroup e hwf
    (fun _ _ _ _ h => layoutRIds_boxes_mirror h) hRemaining hEnv hcontract
  exact regionNotes_c8aGeomT_of_clearance (idSets := idSets) e hwf hClear hEnv hEnvDisj

end Elegant.Layered.PipelineImpl
