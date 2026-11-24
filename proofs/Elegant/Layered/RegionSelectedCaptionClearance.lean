import Elegant.Layered.RegionFlatC7Selected
import Elegant.Layered.RegionFallbackFitProof
import Elegant.Layered.RegionTitleCaptionFit
import Elegant.Layered.RegionPositionsDisjoint
import Elegant.Layered.ExactRunTitleBandClosedProof
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.RegionC5CompoundRank
import Elegant.Layered.RegionSharedAllocation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private abbrev captionTransport {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (r : Rect) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH r)

private theorem captionIndex_eq {α : Type} {xs : List α} {id : α → String}
    (hn : (xs.map id).Nodup) {i j : Nat} {a b : α}
    (ha : xs[i]? = some a) (hb : xs[j]? = some b) (hid : id a = id b) : i = j := by
  have hi : i < (xs.map id).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp ha).1
  apply (List.Nodup.getElem?_inj hi hn).mp
  simp only [List.getElem?_map, ha, hb, Option.map_some, hid]

private theorem captionOwner_at {inp : Input} {source : ModelLabel} {oi : Nat}
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi) :
    ∃ owner : ModelBox, inp.boxes[oi]? = some owner ∧ owner.id = source.owner ∧
      owner.exclusive = false := by
  obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
  exact ⟨_, List.getElem?_eq_getElem hlt, hp.1, hp.2⟩

private theorem caption_emitted {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {l : SceneLabel} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi) :
    l.owner = source.owner ∧ l.rect = sceneCaptionRect execution.params inp o
      execution.lines execution.packedAcc oi source.owner := by
  rw [execution.scene_eq] at hl
  obtain ⟨⟨item, j⟩, hj, hemitted⟩ := List.mem_filterMap.mp hl
  have hj' : inp.labels[j]? = some item := List.mem_zipIdx_iff_getElem?.mp hj
  cases hx : inp.boxes.any (fun box => box.id == item.owner && box.exclusive) with
  | true => simp only [hx, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hmeasure : execution.measured.find? (fun item => item.index == j) with
    | some measured =>
      rw [hmeasure] at hemitted
      have he : l = _ := (Option.some.inj hemitted).symm
      have hsource : l.id = item.id := by rw [he]
      have hji := captionIndex_eq (Elegant.Layered.labelIds_nodup hwf) hj' hi
        (hsource.symm.trans hid)
      rw [hji, hm] at hmeasure
      cases hmeasure
    | none =>
      rw [hmeasure] at hemitted
      cases hf : inp.boxes.findIdx? (fun box => box.id == item.owner && !box.exclusive) with
      | none => rw [hf] at hemitted; cases hemitted
      | some k =>
        rw [hf] at hemitted
        have he : l = _ := (Option.some.inj hemitted).symm
        have hsource : l.id = item.id := by rw [he]
        have hji := captionIndex_eq (Elegant.Layered.labelIds_nodup hwf) hj' hi
          (hsource.symm.trans hid)
        have hitem : item = source := by
          rw [hji, hi] at hj'
          exact Option.some.inj hj'.symm
        subst item
        have hk : k = oi := Option.some.inj (hf.symm.trans ho)
        subst k
        rw [he]
        exact ⟨rfl, rfl⟩

private theorem caption_unmeasured_no_route {P : Params} {m : Measure.Metric}
    {target : Int} {inp : Input} {d : Direction} {measured : List MeasuredLabel}
    (h : measureLabels P m target inp d = .ok measured)
    {i : Nat} {source : ModelLabel} (hi : inp.labels[i]? = some source)
    (hm : measured.find? (fun item => item.index == i) = none) :
    inp.routes.findIdx? (fun route => route.id == source.owner) = none := by
  unfold measureLabels at h
  obtain ⟨options, hoptions, hout⟩ := bind_ok h
  have he := Except.ok.inj hout
  subst measured
  obtain ⟨_, hlookup⟩ := mapM_getElem? _ _ _ hoptions
  have hzip : inp.labels.zipIdx[i]? = some (source, i) := by
    simp only [List.getElem?_zipIdx, hi, Option.map_some, Nat.zero_add]
  obtain ⟨emitted, hstep, hat⟩ := hlookup i (source, i) hzip
  dsimp only at hstep
  cases hr : inp.routes.findIdx? (fun route => route.id == source.owner) with
  | none => rfl
  | some edge =>
    rw [hr] at hstep
    obtain ⟨lines, _, hstep⟩ := bind_ok hstep
    by_cases hover :
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 ∨
        I32_MAX < (lines.length : Int) * P.lineH ∨
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 +
          (if m.profile == .cell then P.slot else 0) ∨
        I32_MAX < (lines.length : Int) * P.lineH +
          (if m.profile == .cell then P.slot else 0)
    · simp only [hover, ↓reduceIte] at hstep
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hstep
    · simp only [hover, ↓reduceIte] at hstep
      have hhit : ∃ label ∈ options.filterMap id, label.index = i := by
        cases d <;> dsimp only at hstep <;>
          rw [← Except.ok.inj hstep] at hat <;>
          exact ⟨_, List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hat, rfl⟩, rfl⟩
      obtain ⟨label, hlabel, hindex⟩ := hhit
      exact False.elim (List.find?_eq_none.mp hm label hlabel (by simp [hindex]))

theorem r7Caption_ownerScope {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {l : SceneLabel} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi) :
    res.scene.layoutDump.labelOwnerAnc l.toLabel =
      source.owner :: res.scene.layoutDump.ancestors source.owner := by
  obtain ⟨howner, _⟩ := caption_emitted execution hwf hl hi hid hm ho
  have hnone := List.findIdx?_eq_none_iff.mp
    (caption_unmeasured_no_route execution.measured_eq hi hm)
  have hfind : res.scene.layoutDump.routes.find? (fun route => route.id == l.toLabel.owner) = none := by
    apply List.find?_eq_none.mpr
    intro route hmem hpred
    rw [execution.scene_eq] at hmem
    change route ∈ inp.routes.zipIdx.map (fun q =>
      Route.mk q.1.id q.1.fromId q.1.toId q.1.orthogonal
        ((execution.packedAcc.routes.getD q.2 []).map
          (fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
            (orientPoint o.direction execution.packedAcc.canvasH p)))) at hmem
    obtain ⟨⟨original, k⟩, hk, rfl⟩ := List.mem_map.mp hmem
    have hsrc : inp.routes[k]? = some original := List.mem_zipIdx_iff_getElem?.mp hk
    change (original.id == l.owner) = true at hpred
    rw [howner, hnone original (List.mem_of_getElem? hsrc)] at hpred
    cases hpred
  rw [Elegant.Layered.labelOwnerAnc_of_no_route hfind]
  change l.owner :: _ = _
  rw [howner]

private theorem captionPacked_size {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have hf (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
      (pairs.foldl packStep start).rects.size = start.rects.size := by
    induction pairs generalizing start with
    | nil => rfl
    | cons pair rest ih => rw [List.foldl_cons, ih, (packStep_sizes start pair).1]
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, hp⟩ := bind_ok h
  rw [← Except.ok.inj hp]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [hf]
  exact execution.components_rects_sizeR

private abbrev captionSceneBox {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (i : Nat) (source : ModelBox) : Box :=
  ⟨source.id, source.role.id, captionTransport execution (execution.packedAcc.rects.getD i default),
    source.parent, source.exclusive⟩

private theorem captionSceneBox_at {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {i : Nat} {source : ModelBox}
    (hi : inp.boxes[i]? = some source) :
    (sceneBoxesExpr execution.params inp o execution.packedAcc)[i]? =
      some (captionSceneBox execution i source) := by
  simp only [sceneBoxesExpr, List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some,
    Nat.zero_add]

private theorem caption_fallback_contained {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hfit : InputFixedFit inp o)
    {l : SceneLabel} {source : ModelLabel} {owner : ModelBox} {i oi : Nat}
    (hi : inp.labels[i]? = some source) (ho : inp.boxes[oi]? = some owner)
    (hownerId : owner.id = source.owner) (hownerEx : owner.exclusive = false)
    (ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) = none)
    (hcaption : l.rect = sceneCaptionRect execution.params inp o
      execution.lines execution.packedAcc oi source.owner) :
    (captionSceneBox execution oi owner).rect.Contained l.rect := by
  have hn := ht
  rw [← hownerId] at hn
  have hc := R_ownerCaptionContainFallbackFit_holds exactIds idSets execution hfit oi owner
    ho hn hownerEx ⟨source, List.mem_of_getElem? hi, hownerId.symm⟩
  have hbox := captionSceneBox_at execution ho
  simp only [sceneCaptionRect, ht, Option.map_none, Option.getD_none] at hcaption
  rw [hcaption]
  simpa only [List.getD_eq_getElem?_getD, hbox, Option.getD_some] using hc

private theorem captionTarget_source {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {b : Box}
    (hb : b ∈ res.scene.layoutDump.boxes) :
    ∃ k original, inp.boxes[k]? = some original ∧ b = captionSceneBox execution k original := by
  change b ∈ res.scene.boxes at hb
  rw [execution.boxes_eq_mapR] at hb
  obtain ⟨⟨original, k⟩, hk, rfl⟩ := List.mem_map.mp hb
  exact ⟨k, original, List.mem_zipIdx_iff_getElem?.mp hk, rfl⟩

private theorem caption_shelves_clear {width : Nat} {gap margin num den : Int}
    {items : List Pack.Item} {packed : Pack.State}
    (hpack : Pack.pack width gap margin num den items = .ok packed)
    {i j : Nat} {a b : Rect} (hi : packed.boxes[i]? = some a)
    (hj : packed.boxes[j]? = some b) (hne : i ≠ j) : Disjoint a b := by
  obtain ⟨hli, hai⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hlj, haj⟩ := List.getElem?_eq_some_iff.mp hj
  have hc := Pack.pack_boxes_disjoint hpack i j hli hlj hne
  rwa [hai, haj] at hc

private theorem caption_gap_of_disjoint {a b : Rect} (h : Disjoint a b) :
    R7_OverlapRowsXGap a b := by
  change ¬ a.meetsInterior b at h
  unfold R7_OverlapRowsXGap Rect.meetsInterior at *
  intro hy ha hb
  omega

def R7_CaptionSharesPart {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (ownerIndex : Nat) (b : Box) : Prop :=
  ∃ (part : List Nat × Part) (k posOwner posTarget targetKey : Nat) (target : ModelBox),
    execution.componentsAcc.parts[k]? = some part ∧
    part.1[posOwner]? = some ownerIndex ∧ part.1[posTarget]? = some targetKey ∧
    inp.boxes[targetKey]? = some target ∧ b = captionSceneBox execution targetKey target

theorem r7Caption_clear_or_sharesPart {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o) {l : SceneLabel} {b : Box} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hb : b ∈ res.scene.layoutDump.boxes)
    (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi) :
    R7_OverlapRowsXGap l.rect b.rect ∨ R7_CaptionSharesPart execution oi b := by
  obtain ⟨owner, howner, hownerId, hownerEx⟩ := captionOwner_at ho
  obtain ⟨_, hcaption⟩ := caption_emitted execution hwf hl hi hid hm ho
  obtain ⟨bi, target, htarget, hbEq⟩ := captionTarget_source execution hb
  have hsize := captionPacked_size execution
  have hbi : bi < execution.packedAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp htarget).1
  have hoi : oi < execution.packedAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp howner).1
  obtain ⟨packed, hpack, hrects, _, htitles, _⟩ :=
    R_packedPartTransportBounded_closed exactIds idSets
      (R_partSizingRResidual_holds exactIds idSets)
      (R_exactTitleCaptionFitB8_holds exactIds idSets) execution
  obtain ⟨kb, pb, posB, _, sb, hpb, hposB, _, hsb, _, hboundB⟩ := hrects bi hbi _ rfl
  have hB : (captionTransport execution sb).Contained b.rect := by
    rw [hbEq]
    exact contained_shiftRect_imp (contained_orientRect hboundB)
  cases ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) with
  | none =>
    have hfitO := caption_fallback_contained execution hfit hi howner hownerId hownerEx ht hcaption
    obtain ⟨ko, po, posO, _, so, hpo, hposO, _, hso, _, hboundO⟩ := hrects oi hoi _ rfl
    by_cases hsame : ko = kb
    · rw [hsame] at hpo
      have hparts : po = pb := Option.some.inj (hpo.symm.trans hpb)
      rw [hparts] at hposO
      exact Or.inr ⟨pb, kb, posO, posB, bi, target, hpb, hposO, hposB, htarget, hbEq⟩
    · have hO : (captionTransport execution so).Contained (captionSceneBox execution oi owner).rect :=
        contained_shiftRect_imp (contained_orientRect hboundO)
      exact Or.inl (caption_gap_of_disjoint (not_meetsInterior_of_contained
        (disjoint_sceneTransport (caption_shelves_clear hpack hso hsb hsame))
        (hO.trans hfitO) hB))
  | some title =>
    have hpred : (title.1 == source.owner) = true :=
      List.find?_some (p := fun row : String × Rect => row.1 == source.owner) ht
    have hsel : title.1 = source.owner := beq_iff_eq.mp hpred
    obtain ⟨stored, hstored, hemp⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some ht)
    cases hs : inp.boxes[stored.1]? with
    | none => simp only [hs] at hemp; cases hemp
    | some titleOwner =>
      simp only [hs] at hemp
      have hpair := Option.some.inj hemp
      have htitleOwner : titleOwner.id = title.1 := congrArg Prod.fst hpair
      have hkey : stored.1 = oi := captionIndex_eq (Model.boxIds_nodup hwf) hs howner
        (htitleOwner.trans (hsel.trans hownerId.symm))
      let size := titleCaptionSize execution.params o (execution.lines.getD stored.1 [])
      have htitleFound :
          captionTransport execution { stored.2 with w := size.w, h := size.h } = title.2 :=
        congrArg Prod.snd hpair
      have htitleRect :
          l.rect = captionTransport execution { stored.2 with w := size.w, h := size.h } := by
        simp only [sceneCaptionRect, ht, Option.map_some, Option.getD_some] at hcaption
        exact hcaption.trans htitleFound.symm
      obtain ⟨ko, po, posO, _localTitle, so, hpo, hposO, _, hso, hstoredEq, hboundO⟩ :=
        htitles stored.1 stored.2 hstored
      rw [hkey] at hposO
      by_cases hsame : ko = kb
      · rw [hsame] at hpo
        have hparts : po = pb := Option.some.inj (hpo.symm.trans hpb)
        rw [hparts] at hposO
        exact Or.inr ⟨pb, kb, posO, posB, bi, target, hpb, hposO, hposB, htarget, hbEq⟩
      · have hO : (captionTransport execution so).Contained l.rect := by
          rw [htitleRect, hstoredEq]
          exact contained_shiftRect_imp (contained_orientRect hboundO)
        exact Or.inl (caption_gap_of_disjoint (not_meetsInterior_of_contained
          (disjoint_sceneTransport (caption_shelves_clear hpack hso hsb hsame)) hO hB))

private theorem captionPlainNode {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {i : Nat} {box : ModelBox}
    (hi : inp.boxes[i]? = some box)
    (hplain : box.role = .node ∨ inp.fixedSizes.any (fun row => row.1 == box.id) = true) :
    ∃ n, execution.graph.nodes[i]? = some n ∧ n.border = 0 := by
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlen : execution.lines.length = inp.boxes.length :=
    (mapM_getElem? _ _ _ hlines).1.trans List.length_zipIdx
  have hli : i < execution.lines.length :=
    hlen.symm ▸ (List.getElem?_eq_some_iff.mp hi).1
  cases hf : inp.fixedSizes.find? (fun entry => entry.1 == box.id) with
  | some entry =>
    obtain ⟨_, _, node, _, _, hnode, hb, _⟩ :=
      measuredGraph_fixed_loop_reservation execution.graph0_eq hli hi hf
    obtain ⟨out, hout, houtb, _, _⟩ := exactGraph_node_key execution.graph_eq hnode
    exact ⟨out, hout, houtb.trans hb⟩
  | none =>
    have hn : inp.fixedSizes.any (fun row => row.1 == box.id) = false :=
      List.any_eq_false.mpr (List.find?_eq_none.mp hf)
    have hr : box.role = .node := by
      rcases hplain with hr | hfixed
      · exact hr
      · rw [hn] at hfixed
        cases hfixed
    obtain ⟨node, hnode, _, hb⟩ := measuredGraph_node_border_zero execution.checked
      execution.graph0_eq (List.getElem?_eq_getElem hli) hi hr hn
    obtain ⟨out, hout, houtb, _, _⟩ := exactGraph_node_key execution.graph_eq hnode
    exact ⟨out, hout, houtb.trans hb⟩

def R7_ActiveFallbackCrossParentSameRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (oi : Nat) (b : Box) : Prop :=
  ∃ (part : List Nat × Part) (k u v bi : Nat) (owner target : ModelBox)
    (candidate : Nat) (chosen : Portfolio.Candidate (Graph × Run))
    (cg : Graph) (run : Run) (spec : RegionSpec) (regions : ComponentRegions),
    execution.componentsAcc.parts[k]? = some part ∧
    part.1[u]? = some oi ∧ part.1[v]? = some bi ∧
    inp.boxes[oi]? = some owner ∧ inp.boxes[bi]? = some target ∧
    b = captionSceneBox execution bi target ∧
    Portfolio.portfolio o.thoroughness
      (componentTrialR execution.params exactIds (r7Spec idSets o execution.params execution.lines)
        inp o execution.graph part.1 execution.measured) = .ok chosen ∧
    chosen.value = (cg, run) ∧
    some spec = r7Spec idSets o execution.params execution.lines ∧
    newComponentRegions (some spec) execution.params inp (componentGraph execution.graph part.1) =
      .ok (some regions) ∧
    componentRunR execution.params (exactDecls exactIds inp) (some spec) inp
      (componentCandidateR (some spec) execution.graph part.1 candidate)
      execution.measured (candidateOrder candidate) = .ok (cg, run) ∧
    owner.parent ≠ target.parent ∧
    (rk run.proper.rank u).toNat = (rk run.proper.rank v).toNat

private theorem captionRun_nodes {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {inputGraph cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {options : OrderOptions}
    (hrun : componentRunR P exact spec inp inputGraph labels options = .ok (cg, run)) :
    cg.nodes = inputGraph.nodes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hrank⟩
  · rw [he]
  · exact rankEquivalentR_nodes_eq hrank

private theorem caption_plain_frames_transport {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} {k u v oi bi : Nat} {owner target : ModelBox}
    {cg : Graph} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hk : execution.componentsAcc.parts[k]? = some part)
    (hu : part.1[u]? = some oi) (hv : part.1[v]? = some bi)
    (ho : inp.boxes[oi]? = some owner) (hbi : inp.boxes[bi]? = some target)
    (hplaced : part.2 =
      { placeComponentExact execution.params cg run 0 execution.measured loops with area := area })
    (hnu : u < cg.nodes.length) (hnv : v < cg.nodes.length)
    (hframes : Disjoint (frameRect execution.params cg run u) (frameRect execution.params cg run v)) :
    Disjoint (captionSceneBox execution oi owner).rect
      (captionSceneBox execution bi target).rect := by
  obtain ⟨packed, hpack, _⟩ := packAcc_components_disjoint execution.packed_eq
  have hkLen : k < packed.boxes.length := by
    rw [Pack.pack_count hpack, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  have hshelf : packed.boxes[k]? = some packed.boxes[k] := List.getElem?_eq_getElem hkLen
  have hs : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some (part, packed.boxes[k]) := List.getElem?_zip_eq_some.mpr ⟨hk, hshelf⟩
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  have hframeAt {j key : Nat} (hkey : part.1[j]? = some key)
      (hj : j < cg.nodes.length) (hkeyLen : key < inp.boxes.length) :
      execution.packedAcc.rects.getD key default = shiftRect packed.boxes[k].x packed.boxes[k].y
        (shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect execution.params cg run j)) := by
    let localRect : Rect :=
      shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect execution.params cg run j)
    have hpartRect : part.2.rects[j]? = some localRect := by
      rw [hplaced]
      change (((List.range cg.nodes.length).map (frameRect execution.params cg run)).map
        (shiftRect (0 - bounds.minX) (-bounds.minY)))[j]? = some localRect
      simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, localRect]
    have hentry : (part.1.zip part.2.rects)[j]? = some (key, localRect) :=
      List.getElem?_zip_eq_some.mpr ⟨hkey, hpartRect⟩
    have hsize : key < execution.componentsAcc.rects.size :=
      execution.components_rects_sizeR.symm ▸ hkeyLen
    exact actual_components_packed_rect_valueR (by rfl) execution.components_eq
      execution.packed_eq packed hpack hs hentry hsize default
  have hrectO := hframeAt hu hnu (List.getElem?_eq_some_iff.mp ho).1
  have hrectB := hframeAt hv hnv (List.getElem?_eq_some_iff.mp hbi).1
  change Disjoint (captionTransport execution (execution.packedAcc.rects.getD oi default))
    (captionTransport execution (execution.packedAcc.rects.getD bi default))
  rw [hrectO, hrectB]
  exact disjoint_sceneTransport
    (not_meetsInterior_shiftRect (not_meetsInterior_shiftRect hframes))

def R7_FallbackOwnerDemoted (inp : Input) (oi : Nat) : Prop :=
  ∃ owner, inp.boxes[oi]? = some owner ∧ owner.role = .group ∧
    inp.fixedSizes.any (fun row => row.1 == owner.id) = true

theorem r7Caption_activeFallback_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o) {l : SceneLabel} {b : Box} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hex : b.exclusive = true)
    (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi)
    (ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) = none)
    (hactive : R7_ActiveFallbackCrossParentSameRank execution oi b) :
    R7_OverlapRowsXGap l.rect b.rect := by
  obtain ⟨part, k, u, v, bi, owner, target, candidate, chosen, cg, run, spec, regions,
    hk, hu, hv, howner, htarget, hb, hchosen, hvalue, _, hregions, hrun, hparent, hrank⟩ :=
    hactive
  obtain ⟨found, hfound, hownerId, hownerEx⟩ := captionOwner_at ho
  have hfoundEq : found = owner := Option.some.inj (hfound.symm.trans howner)
  rw [hfoundEq] at hownerId hownerEx
  have htitleNone := ht
  rw [← hownerId] at htitleNone
  have hownerPlain := R_fallbackOwnerCasesW_holds exactIds idSets
    (R_nonfixedGroupTitle_holds exactIds idSets) execution hwf howner htitleNone
  have htargetEx : target.exclusive = true := by simpa only [hb] using hex
  have htargetRole : target.role = .node := by
    have hn := wellFormed_exclusive_not_group hwf (List.mem_of_getElem? htarget) htargetEx
    cases hr : target.role with
    | node => rfl
    | group => exact False.elim (hn hr)
  obtain ⟨ownerNode, hownerNode, hownerBorder⟩ :=
    captionPlainNode execution howner hownerPlain
  obtain ⟨targetNode, htargetNode, htargetBorder⟩ :=
    captionPlainNode execution htarget (Or.inl htargetRole)
  have hnodes := captionRun_nodes hrun
  have hnu : cg.nodes[u]? = some ownerNode := by
    rw [hnodes]
    exact component_node_lookupR hu hownerNode
  have hnv : cg.nodes[v]? = some targetNode := by
    rw [hnodes]
    exact component_node_lookupR hv htargetNode
  have hne : u ≠ v := by
    intro he
    rw [he, hv] at hu
    have hkey := Option.some.inj hu
    rw [hkey, howner] at htarget
    exact hparent (congrArg ModelBox.parent (Option.some.inj htarget))
  have hresolved : newComponentRegions (some spec) execution.params inp
      (componentCandidateR (some spec) execution.graph part.1 candidate) = .ok (some regions) :=
    componentTrialR_selected_regions candidate hregions
  have hlocalGap := componentRunR_active_plain_same_rank_gap (exactIds := exactIds)
    execution.checked hrun hresolved hnu hnv hownerBorder htargetBorder hne hrank
  have hlocal : Disjoint (frameRect execution.params cg run u)
      (frameRect execution.params cg run v) := by
    unfold R8a_OverlapRowsXGap at hlocalGap
    unfold Disjoint Rect.meetsInterior
    rintro ⟨hx, hy⟩
    have hgap := hlocalGap hy (by omega) (by omega)
    omega
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  obtain ⟨_, placedChosen, placedGraph, placedRun, loops, area, _, _, hplacedChosen, hplacedValue,
    _, _, _, hplaced⟩ := hall part (List.mem_of_getElem? hk)
  have hchosenEq : placedChosen = chosen := Except.ok.inj (hplacedChosen.symm.trans hchosen)
  have hvalueEq : (placedGraph, placedRun) = (cg, run) := by
    rw [← hplacedValue, hchosenEq, hvalue]
  have hgraphEq : placedGraph = cg := congrArg Prod.fst hvalueEq
  have hrunEq : placedRun = run := congrArg Prod.snd hvalueEq
  rw [hgraphEq, hrunEq] at hplaced
  have hclear : Disjoint (captionSceneBox execution oi owner).rect b.rect := by
    rw [hb]
    exact caption_plain_frames_transport execution hk hu hv howner htarget
      (area := area) hplaced (List.getElem?_eq_some_iff.mp hnu).1
      (List.getElem?_eq_some_iff.mp hnv).1 hlocal
  obtain ⟨_, hcaption⟩ := caption_emitted execution hwf hl hi hid hm ho
  have hcontained :=
    caption_fallback_contained execution hfit hi howner hownerId hownerEx ht hcaption
  exact caption_gap_of_disjoint
    (not_meetsInterior_of_contained hclear hcontained (Rect.Contained.refl _))

theorem r7Caption_demotedFallback_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o) {l : SceneLabel} {b : Box} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hex : b.exclusive = true)
    (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi)
    (ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) = none)
    (hactive : R7_ActiveFallbackCrossParentSameRank execution oi b)
    (_hdemoted : R7_FallbackOwnerDemoted inp oi) :
    R7_OverlapRowsXGap l.rect b.rect :=
  r7Caption_activeFallback_clear execution hwf hfit hl hex hi hid hm ho ht hactive

private theorem caption_fallback_plain_frames {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {source : ModelLabel} {oi : Nat} {owner : ModelBox} {b : Box}
    (ho : inp.boxes[oi]? = some owner) (howner : owner.id = source.owner)
    (hownerEx : owner.exclusive = false) (hbEx : b.exclusive = true)
    (ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) = none)
    (hshared : R7_CaptionSharesPart execution oi b) :
    Disjoint (captionSceneBox execution oi owner).rect b.rect ∨
      R7_ActiveFallbackCrossParentSameRank execution oi b := by
  obtain ⟨part, k, u, v, bi, target, hk, hu, hv, hbi, hb⟩ := hshared
  have ht' := ht
  rw [← howner] at ht'
  have hownerPlain := R_fallbackOwnerCasesW_holds exactIds idSets
    (R_nonfixedGroupTitle_holds exactIds idSets) execution hwf ho ht'
  have htargetEx : target.exclusive = true := by simpa only [hb] using hbEx
  have htargetPlain : target.role = .node := by
    have hn := wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hbi) htargetEx
    cases hr : target.role with
    | node => rfl
    | group => exact False.elim (hn hr)
  obtain ⟨no, hno, hbo⟩ := captionPlainNode execution ho hownerPlain
  obtain ⟨nb, hnb, hbb⟩ := captionPlainNode execution hbi (Or.inl htargetPlain)
  have hne : u ≠ v := by
    intro huv
    rw [huv, hv] at hu
    have hkey := Option.some.inj hu
    rw [hkey, ho] at hbi
    have hs := Option.some.inj hbi
    rw [← hs, hownerEx] at htargetEx
    cases htargetEx
  obtain ⟨hkeys, hactual⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  have hpart := List.mem_of_getElem? hk
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hkeys]
    exact List.mem_map_of_mem hpart
  obtain ⟨candidate, chosen, cg, run, loops, area, spec, _, hchosen, hvalue,
    hregions, hrun, _, hplaced⟩ := hactual part hpart
  have hnodes := captionRun_nodes hrun
  have hnu : cg.nodes[u]? = some no := by rw [hnodes]; exact component_node_lookupR hu hno
  have hnv : cg.nodes[v]? = some nb := by rw [hnodes]; exact component_node_lookupR hv hnb
  have hframes : Disjoint (frameRect execution.params cg run u)
      (frameRect execution.params cg run v) ∨
        R7_ActiveFallbackCrossParentSameRank execution oi b := by
    cases spec with
    | none =>
      rw [componentCandidateR_none] at hrun
      exact Or.inl (componentRunR_positions_disjointR_none execution.graph0_eq execution.graph_eq
        hcomp hrun hnu hnv hbo hbb hne)
    | some spec =>
      by_cases hp : owner.parent = target.parent
      · exact Or.inl (componentRunR_region_siblings_disjoint execution.graph0_eq execution.graph_eq
          hrun hne hu hv hno hnb ho hbi hbo hbb hp)
      · by_cases hr : (rk run.proper.rank u).toNat = (rk run.proper.rank v).toNat
        · obtain ⟨regions, hregions, hspec⟩ := hregions
          change some spec = (if regions.isSome then
            r7Spec idSets o execution.params execution.lines else none) at hspec
          cases regions with
          | none => simp at hspec
          | some regions =>
            have hspec' : some spec = r7Spec idSets o execution.params execution.lines := hspec
            change newComponentRegions (r7Spec idSets o execution.params execution.lines)
              execution.params inp (componentGraph execution.graph part.1) =
              .ok (some regions) at hregions
            rw [← hspec'] at hregions
            exact Or.inr ⟨part, k, u, v, bi, owner, target, candidate, chosen, cg, run, spec, regions,
              hk, hu, hv, ho, hbi, hb, hchosen, hvalue, hspec', hregions, hrun, hp, hr⟩
        · exact Or.inl (componentRunR_positions_disjointR_different_rank (exactIds := exactIds)
            hrun hnu hnv hbo hbb hr)
  rcases hframes with hframes | hopen
  · apply Or.inl
    rw [hb]
    exact caption_plain_frames_transport execution hk hu hv ho hbi hplaced
      (List.getElem?_eq_some_iff.mp hnu).1 (List.getElem?_eq_some_iff.mp hnv).1 hframes
  · exact Or.inr hopen

private theorem caption_ancestor_has_child {d : LayoutDump} {anc id : String} {fuel : Nat}
    (h : anc ∈ LayoutDump.ancestors.go d fuel id) :
    ∃ child ∈ d.boxes, child.parent = anc ∧ anc ≠ "" := by
  induction fuel generalizing id with
  | zero =>
    change anc ∈ ([] : List String) at h
    cases h
  | succ n ih =>
    cases hf : d.boxes.find? (fun b => b.id == id) with
    | none =>
      simp only [LayoutDump.ancestors.go, LayoutDump.box?, hf] at h
      cases h
    | some b =>
      by_cases hp : b.parent = ""
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hf, hp, ↓reduceIte] at h
        cases h
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hf, hp, ↓reduceIte] at h
        rcases List.mem_cons.mp h with he | hm
        · exact ⟨b, List.mem_of_find?_eq_some hf, he.symm, he.symm ▸ hp⟩
        · exact ih hm

theorem r7Caption_fallback_has_no_descendant {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {source : ModelLabel} {oi : Nat} {b : Box}
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi)
    (ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) = none) :
    source.owner ∉ res.scene.layoutDump.ancestors b.id := by
  intro h
  obtain ⟨owner, howner, hid, _⟩ := captionOwner_at ho
  have hwalk : source.owner ∈ LayoutDump.ancestors.go res.scene.layoutDump
      res.scene.layoutDump.boxes.length b.id := h
  obtain ⟨child, hm, hp, hnonempty⟩ := caption_ancestor_has_child hwalk
  obtain ⟨_, childSource, hc, hceq⟩ := captionTarget_source execution hm
  have hparent : childSource.parent = source.owner := by
    rw [hceq] at hp
    exact hp
  obtain ⟨par, hpar, hpid, hgroup, hnotFixed⟩ := framedParents_parent hfp
    (List.mem_of_getElem? hc) (by rw [hparent]; exact hnonempty)
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpar
  have hkey : pi = oi := captionIndex_eq (Model.boxIds_nodup hwf) hpi howner
    (hpid.trans (hparent.trans hid.symm))
  rw [hkey, howner] at hpi
  have he : par = owner := (Option.some.inj hpi).symm
  subst par
  have hhit := R_nonfixedGroupTitle_holds exactIds idSets execution howner hgroup hnotFixed
  rw [hid, ht] at hhit
  cases hhit

def R7_SelectedCaptionObligation {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (index : Nat) (source : ModelLabel),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    inp.labels[index]? = some source → l.id = source.id →
    execution.measured.find? (fun item => item.index == index) = none →
    (∃ oi, inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi) →
    R7_OverlapRowsXGap l.rect b.rect

def R7_SelectedCaptionResidual {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (index oi : Nat) (source : ModelLabel),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ source.owner :: res.scene.layoutDump.ancestors source.owner →
    inp.labels[index]? = some source → l.id = source.id →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi →
    max l.rect.y b.rect.y < min (l.rect.y + l.rect.h) (b.rect.y + b.rect.h) →
    0 < l.rect.w → 0 < b.rect.w →
    (let title := (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun row => row.1 == source.owner)
     (title.isSome = true ∧ R7_CaptionSharesPart execution oi b) ∨
       (title = none ∧ source.owner ∉ res.scene.layoutDump.ancestors b.id ∧
         R7_ActiveFallbackCrossParentSameRank execution oi b)) →
    l.rect.x + l.rect.w ≤ b.rect.x ∨ b.rect.x + b.rect.w ≤ l.rect.x

theorem r7Caption_iff_selectedResidual {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hfit : InputFixedFit inp o) :
    R7_SelectedCaptionObligation execution ↔ R7_SelectedCaptionResidual execution := by
  constructor
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw _
    have hscope' := r7Caption_ownerScope execution hwf hl hi hid hm ho
    exact h l b i source hl hb hex (by rwa [hscope']) hi hid hm ⟨oi, ho⟩ hrows hlw hbw
  · intro h l b i source hl hb hex hscope hi hid hm ⟨oi, ho⟩ hrows hlw hbw
    have hscope' : b.id ∉ source.owner :: res.scene.layoutDump.ancestors source.owner := by
      rw [r7Caption_ownerScope execution hwf hl hi hid hm ho] at hscope
      exact hscope
    rcases r7Caption_clear_or_sharesPart execution hwf hfit hl hb hi hid hm ho with
      hgap | hshared
    · exact hgap hrows hlw hbw
    · cases ht : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun row => row.1 == source.owner) with
      | some title =>
        have htSome : ((sceneTitlesExpr execution.params inp o execution.lines
            execution.packedAcc).find? (fun row => row.1 == source.owner)).isSome = true := by
          rw [ht]
          rfl
        exact h l b i oi source hl hb hex hscope' hi hid hm ho hrows hlw hbw
          (Or.inl ⟨htSome, hshared⟩)
      | none =>
        obtain ⟨owner, howner, hownerId, hownerEx⟩ := captionOwner_at ho
        rcases caption_fallback_plain_frames execution hwf howner hownerId hownerEx hex ht
          hshared with hclear | hactive
        · obtain ⟨_, hcaption⟩ := caption_emitted execution hwf hl hi hid hm ho
          have hfitO := caption_fallback_contained execution hfit hi howner hownerId hownerEx ht hcaption
          have hgap := caption_gap_of_disjoint
            (not_meetsInterior_of_contained hclear hfitO (Rect.Contained.refl _))
          exact hgap hrows hlw hbw
        · exact h l b i oi source hl hb hex hscope' hi hid hm ho hrows hlw hbw
            (Or.inr ⟨ht, r7Caption_fallback_has_no_descendant execution hwf hfp (b := b) ho ht,
              hactive⟩)

def R7_SelectedCaptionAfterDemotedResidual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (index oi : Nat) (source : ModelLabel),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ source.owner :: res.scene.layoutDump.ancestors source.owner →
    inp.labels[index]? = some source → l.id = source.id →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi →
    max l.rect.y b.rect.y < min (l.rect.y + l.rect.h) (b.rect.y + b.rect.h) →
    0 < l.rect.w → 0 < b.rect.w →
    (let title := (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun row => row.1 == source.owner)
     (title.isSome = true ∧ R7_CaptionSharesPart execution oi b) ∨
       (title = none ∧ source.owner ∉ res.scene.layoutDump.ancestors b.id ∧
         R7_ActiveFallbackCrossParentSameRank execution oi b ∧
         ¬ R7_FallbackOwnerDemoted inp oi)) →
    l.rect.x + l.rect.w ≤ b.rect.x ∨ b.rect.x + b.rect.w ≤ l.rect.x

theorem r7Caption_selectedResidual_iff_afterDemoted {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfit : InputFixedFit inp o) :
    R7_SelectedCaptionResidual execution ↔ R7_SelectedCaptionAfterDemotedResidual execution := by
  constructor
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    apply h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
    rcases hcase with htitle | ⟨ht, hanc, hactive, _⟩
    · exact Or.inl htitle
    · exact Or.inr ⟨ht, hanc, hactive⟩
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    rcases hcase with htitle | ⟨ht, hanc, hactive⟩
    · exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw (Or.inl htitle)
    · by_cases hdemoted : R7_FallbackOwnerDemoted inp oi
      · exact r7Caption_demotedFallback_clear execution hwf hfit hl hex hi hid hm ho ht
          hactive hdemoted hrows hlw hbw
      · exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
          (Or.inr ⟨ht, hanc, hactive, hdemoted⟩)

theorem r7Caption_iff_afterDemotedResidual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hfit : InputFixedFit inp o) :
    R7_SelectedCaptionObligation execution ↔
      R7_SelectedCaptionAfterDemotedResidual execution :=
  (r7Caption_iff_selectedResidual execution hwf hfp hfit).trans
    (r7Caption_selectedResidual_iff_afterDemoted execution hwf hfit)

def R7_SelectedRouteObligation {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (pair : R7_SelectedRoutePair execution l b),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel → ¬ R7_SelectedSettledLoop pair →
    R7_OverlapRowsXGap pair.rect
      (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target)

theorem r7SelectedClearance_caption_restrict {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hfit : InputFixedFit inp o)
    (hroute : R7_SelectedRouteWithPlainTarget execution)
    (hcaption : R7_SelectedCaptionResidual execution) : R7_SelectedClearance execution :=
  ⟨hroute, (r7Caption_iff_selectedResidual execution hwf hfp hfit).mpr hcaption⟩

def R7_ReindexedSelectedCaptionRestricted (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
    Elegant.Layered.PartsSeparated inp o res → LabelRunsClearExclusiveBoxes inp o res →
    SceneCaptionBoxContainment inp o res →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
      R7_SelectedRouteWithPlainTarget execution ∧ R7_SelectedCaptionResidual execution

theorem r7_reindexedSelectedClearance_iff_captionRestricted (exactIds : List String)
    (idSets : List (String × List String)) :
    R7_ReindexedSelectedClearance exactIds idSets ↔
      R7_ReindexedSelectedCaptionRestricted exactIds idSets := by
  constructor
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    have hclear := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hclear.route, (r7Caption_iff_selectedResidual execution hwf hfp hfit).mp hclear.caption⟩
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact r7SelectedClearance_caption_restrict execution hwf hfp hfit hroute hcaption

theorem flatC7B_layoutRIds_reindex_iff_captionRestricted (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC7B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R7_ReindexedSelectedCaptionRestricted exactIds idSets :=
  (flatC7B_layoutRIds_reindex_iff_selected exactIds idSets).trans
    (r7_reindexedSelectedClearance_iff_captionRestricted exactIds idSets)



def R7_ReindexedSelectedCaptionAfterDemoted (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
    Elegant.Layered.PartsSeparated inp o res → LabelRunsClearExclusiveBoxes inp o res →
    SceneCaptionBoxContainment inp o res →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
      R7_SelectedRouteWithPlainTarget execution ∧ R7_SelectedCaptionAfterDemotedResidual execution

theorem r7_reindexedCaptionRestricted_iff_afterDemoted (exactIds : List String)
    (idSets : List (String × List String)) :
    R7_ReindexedSelectedCaptionRestricted exactIds idSets ↔
      R7_ReindexedSelectedCaptionAfterDemoted exactIds idSets := by
  constructor
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hroute, (r7Caption_selectedResidual_iff_afterDemoted execution hwf hfit).mp hcaption⟩
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hroute, (r7Caption_selectedResidual_iff_afterDemoted execution hwf hfit).mpr hcaption⟩

theorem flatC7B_layoutRIds_reindex_iff_captionAfterDemoted (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC7B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R7_ReindexedSelectedCaptionAfterDemoted exactIds idSets :=
  (flatC7B_layoutRIds_reindex_iff_captionRestricted exactIds idSets).trans
    (r7_reindexedCaptionRestricted_iff_afterDemoted exactIds idSets)

private abbrev installedCaptionSize {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (key : Nat) (r : Rect) : Rect :=
  let size := titleCaptionSize execution.params o (execution.lines.getD key [])
  { r with w := size.w, h := size.h }

private theorem installed_part_index_eq {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {p q : List Nat × Part} {i j key : Nat}
    (hi : execution.componentsAcc.parts[i]? = some p)
    (hj : execution.componentsAcc.parts[j]? = some q)
    (hp : key ∈ p.1) (hq : key ∈ q.1) : i = j := by
  have hmap := (actual_components_parts_geometryR (by rfl) execution.components_eq).1
  have hpi : p.1 ∈ components execution.graph := by
    rw [← hmap]
    exact List.mem_map_of_mem (List.mem_of_getElem? hi)
  have hqj : q.1 ∈ components execution.graph := by
    rw [← hmap]
    exact List.mem_map_of_mem (List.mem_of_getElem? hj)
  have hnodup := actual_components_parts_keys_nodupR (by rfl) execution.components_eq
  have hbound : i < (execution.componentsAcc.parts.map Prod.fst).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hi).1
  have hkey : p.1 = q.1 := components_shared_member_eq hpi hqj hp hq
  apply (List.Nodup.getElem?_inj hbound hnodup).mp
  simp only [List.getElem?_map, hi, hj, Option.map_some, hkey]

structure R7_InstalledCaptionPair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (oi : Nat)
    (l : SceneLabel) (b : Box) where
  part : List Nat × Part
  index : Nat
  shelf : Rect
  packed : Pack.State
  candidate : Nat
  chosen : Portfolio.Candidate (Graph × Run)
  spec : Option RegionSpec
  cg : Graph
  run : Run
  loops : List (Nat × LoopPlacement)
  area : Int
  raw : Nat × Rect
  topNode : Node
  targetPos : Nat
  targetKey : Nat
  targetNode : Node
  targetSource : ModelBox
  shelf_eq : (execution.componentsAcc.parts.zip packed.boxes)[index]? = some (part, shelf)
  pack_eq : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
    execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
    (LayoutConst.component_aspect_den.get o.profile)
    (execution.componentsAcc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) = .ok packed
  chosen_eq : Portfolio.portfolio o.thoroughness
    (componentTrialR execution.params exactIds (r7Spec idSets o execution.params execution.lines)
      inp o execution.graph part.1 execution.measured) = .ok chosen
  winner_eq : chosen.value = (cg, run)
  effective_eq : ∃ rs, newComponentRegions (r7Spec idSets o execution.params execution.lines)
    execution.params inp (componentGraph execution.graph part.1) = .ok rs ∧
    spec = r7Eff idSets o execution.params execution.lines rs
  run_eq : componentRunR execution.params (exactDecls exactIds inp) spec inp
    (componentCandidateR spec execution.graph part.1 candidate)
    execution.measured (candidateOrder candidate) = .ok (cg, run)
  loops_eq : componentLoops execution.params cg run execution.measured = .ok loops
  part_eq : part.2 = { placeComponentExact execution.params cg run 0
    execution.measured loops with area := area }
  owner_pos : part.1[raw.1]? = some oi
  top_eq : cg.nodes[raw.1]? = some topNode
  top_border : topNode.border = -2
  top_mem : raw ∈ componentTitles execution.params cg run
  target_pos : part.1[targetPos]? = some targetKey
  target_eq : cg.nodes[targetPos]? = some targetNode
  target_plain : targetNode.border = 0
  target_source : inp.boxes[targetKey]? = some targetSource
  target_exclusive : targetSource.exclusive = true
  label_rect : l.rect = r7SelectedTransport execution shelf cg run loops
    (installedCaptionSize execution oi raw.2)
  box_rect : b.rect = r7SelectedTransport execution shelf cg run loops
    (frameRect execution.params cg run targetPos)

theorem r7Caption_installed_selectedPair {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {l : SceneLabel} {b : Box} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hex : b.exclusive = true)
    (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi)
    (ht : ((sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner)).isSome = true)
    (hshared : R7_CaptionSharesPart execution oi b) :
    Nonempty (R7_InstalledCaptionPair execution oi l b) := by
  obtain ⟨owner, howner, hownerId, _⟩ := captionOwner_at ho
  obtain ⟨_, hcaption⟩ := caption_emitted execution hwf hl hi hid hm ho
  obtain ⟨part, k, u, v, key, target, hk, hu, hv, htarget, hb⟩ := hshared
  cases hfind : (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner) with
  | none => rw [hfind] at ht; cases ht
  | some title =>
    have hsel : title.1 = source.owner := beq_iff_eq.mp
      (List.find?_some (p := fun row : String × Rect => row.1 == source.owner) hfind)
    obtain ⟨stored, hstored, hemitted⟩ :=
      List.mem_filterMap.mp (List.mem_of_find?_eq_some hfind)
    cases hs : inp.boxes[stored.1]? with
    | none => simp only [hs] at hemitted; cases hemitted
    | some titleOwner =>
      simp only [hs] at hemitted
      have hpair := Option.some.inj hemitted
      have heKey : stored.1 = oi := captionIndex_eq (Model.boxIds_nodup hwf) hs howner
        ((congrArg Prod.fst hpair).trans (hsel.trans hownerId.symm))
      have htitle : l.rect = captionTransport execution (installedCaptionSize execution oi stored.2) := by
        simp only [sceneCaptionRect, hfind, Option.map_some, Option.getD_some] at hcaption
        have hrect : captionTransport execution
            (installedCaptionSize execution stored.1 stored.2) = title.2 :=
          congrArg Prod.snd hpair
        rw [heKey] at hrect
        exact hcaption.trans hrect.symm
      obtain ⟨packed, hpack, _, _, htitles, _⟩ :=
        R_packedPartTransportBounded_closed exactIds idSets
          (R_partSizingRResidual_holds exactIds idSets)
          (R_exactTitleCaptionFitB8_holds exactIds idSets) execution
      obtain ⟨kt, tp, pos, stored0, shelf, htp, hp, hmem, hshelf, hr, _⟩ :=
        htitles stored.1 stored.2 hstored
      rw [heKey] at hp
      have hiEq := installed_part_index_eq execution htp hk
        (List.mem_of_getElem? hp) (List.mem_of_getElem? hu)
      subst kt
      have hePart : tp = part := Option.some.inj (htp.symm.trans hk)
      subst tp
      have hj : (execution.componentsAcc.parts.zip packed.boxes)[k]? = some (part, shelf) :=
        List.getElem?_zip_eq_some.mpr ⟨hk, hshelf⟩
      obtain ⟨candidate, chosen, cg, run, loops, area, spec, _, hchosen, hvalue,
        hregions, hrun, hloops, hplaced⟩ :=
        (actual_components_parts_geometryR (by rfl) execution.components_eq).2 part
          (List.mem_of_getElem? hk)
      let bounds := placeBoundsX execution.params cg run execution.measured loops
      have hmem' : (pos, stored0) ∈ (componentTitles execution.params cg run).map
          (fun t => (t.1, shiftRect (0 - bounds.minX) (-bounds.minY) t.2)) := by
        rw [hplaced] at hmem
        exact hmem
      obtain ⟨raw, hraw, hrawPlaced⟩ := List.mem_map.mp hmem'
      have hrawPos : raw.1 = pos := congrArg Prod.fst hrawPlaced
      have hrawRect : shiftRect (0 - bounds.minX) (-bounds.minY) raw.2 = stored0 :=
        congrArg Prod.snd hrawPlaced
      obtain ⟨top, htop, htopBorder, htopPos, _, _⟩ :=
        componentTitles_dimension_source execution.params cg run hraw
      have htopEq : cg.nodes[raw.1]? = some top.1 := by
        rw [htopPos]
        exact List.mem_zipIdx_iff_getElem?.mp htop
      have htargetEx : target.exclusive = true := by simpa only [hb] using hex
      have htargetRole : target.role = .node := by
        have hn := wellFormed_exclusive_not_group hwf (List.mem_of_getElem? htarget) htargetEx
        cases he : target.role with
        | node => rfl
        | group => exact False.elim (hn he)
      obtain ⟨targetNode, htargetGraph, htargetPlain⟩ :=
        captionPlainNode execution htarget (Or.inl htargetRole)
      have htargetNode : cg.nodes[v]? = some targetNode := by
        rw [captionRun_nodes hrun]
        exact component_node_lookupR hv htargetGraph
      have hvLen := (List.getElem?_eq_some_iff.mp htargetNode).1
      let partFrame := shiftRect (0 - bounds.minX) (-bounds.minY)
        (frameRect execution.params cg run v)
      have hplacedRect : part.2.rects[v]? = some partFrame := by
        rw [hplaced]
        change (((List.range cg.nodes.length).map (frameRect execution.params cg run)).map
          (shiftRect (0 - bounds.minX) (-bounds.minY)))[v]? = some partFrame
        simp only [List.getElem?_map, List.getElem?_range hvLen, Option.map_some, partFrame]
      have hentry : (part.1.zip part.2.rects)[v]? = some (key, partFrame) :=
        List.getElem?_zip_eq_some.mpr ⟨hv, hplacedRect⟩
      have hsize : key < execution.componentsAcc.rects.size :=
        execution.components_rects_sizeR.symm ▸ (List.getElem?_eq_some_iff.mp htarget).1
      have hpackedRect := actual_components_packed_rect_valueR (by rfl) execution.components_eq
        execution.packed_eq packed hpack hj hentry hsize default
      have hbox : b.rect = r7SelectedTransport execution shelf cg run loops
          (frameRect execution.params cg run v) := by
        rw [hb]
        change captionTransport execution (execution.packedAcc.rects.getD key default) = _
        rw [hpackedRect]
        unfold r7SelectedTransport
        dsimp only [partFrame]
        rw [shiftRect_shiftRect]
      have hlRect : l.rect = r7SelectedTransport execution shelf cg run loops
          (installedCaptionSize execution oi raw.2) := by
        rw [htitle, hr, ← hrawRect]
        have hcomm (x y : Int) (rect : Rect) :
            installedCaptionSize execution oi (shiftRect x y rect) =
              shiftRect x y (installedCaptionSize execution oi rect) := by cases rect; rfl
        unfold r7SelectedTransport
        rw [hcomm, hcomm, shiftRect_shiftRect]
      exact ⟨{
        part := part, index := k, shelf := shelf, packed := packed, candidate := candidate
        chosen := chosen, spec := spec, cg := cg, run := run, loops := loops, area := area
        raw := raw, topNode := top.1, targetPos := v, targetKey := key
        targetNode := targetNode, targetSource := target
        shelf_eq := hj, pack_eq := hpack, chosen_eq := hchosen, winner_eq := hvalue
        effective_eq := hregions, run_eq := hrun, loops_eq := hloops, part_eq := hplaced
        owner_pos := hrawPos.symm ▸ hp, top_eq := htopEq, top_border := htopBorder, top_mem := hraw
        target_pos := hv, target_eq := htargetNode, target_plain := htargetPlain
        target_source := htarget, target_exclusive := htargetEx, label_rect := hlRect,
        box_rect := hbox }⟩

theorem r7Caption_installed_no_regions {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionR exactIds [] inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {l : SceneLabel} {b : Box} {oi : Nat} (pair : R7_InstalledCaptionPair execution oi l b) :
    R7_OverlapRowsXGap l.rect b.rect := by
  have hcomponents := execution.components_eq
  simp only [List.isEmpty_nil, ↓reduceIte, layoutComponentR_none] at hcomponents
  let exactExecution : SceneExecutionX exactIds inp o res :=
    ⟨execution.params, execution.metric, execution.lines, execution.measured,
      execution.graph0, execution.graph, execution.componentsAcc, execution.packedAcc,
      execution.checked, execution.metric_eq, execution.lines_eq, execution.measured_eq,
      execution.graph0_eq, execution.graph_eq, hcomponents, execution.packed_eq, execution.scene_eq⟩
  obtain ⟨rs, _, heff⟩ := pair.effective_eq
  have hnone : pair.spec = none := by
    rw [heff]
    cases rs <;> rfl
  let cg := componentCandidate execution.graph pair.part.1 pair.candidate
  have hr := pair.run_eq
  rw [hnone, componentCandidateR_none, componentRunR_none] at hr
  change (componentRunX execution.params (exactDecls exactIds inp) cg
    execution.measured (candidateOrder pair.candidate)).map (fun run => (cg, run)) =
    .ok (pair.cg, pair.run) at hr
  have hc : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured (candidateOrder pair.candidate) = .ok pair.run ∧ cg = pair.cg := by
    cases h : componentRunX execution.params (exactDecls exactIds inp) cg
        execution.measured (candidateOrder pair.candidate) with
    | error e => simp [h, Except.map] at hr
    | ok run =>
      rw [h] at hr
      have he : (cg, run) = (pair.cg, pair.run) := Except.ok.inj hr
      exact ⟨congrArg Except.ok (congrArg Prod.snd he), congrArg Prod.fst he⟩
  have hpart := (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem (List.mem_of_getElem? hpart)
  have htop : cg.nodes[pair.raw.1]? = some pair.topNode := by rw [hc.2]; exact pair.top_eq
  have ht : pair.raw ∈ componentTitles execution.params cg pair.run := by
    rw [hc.2]; exact pair.top_mem
  have hb : cg.nodes[pair.targetPos]? = some pair.targetNode := by rw [hc.2]; exact pair.target_eq
  have hclear := x_runTitleBandClearXW_holds exactIds exactExecution hwf hfp hcomp hc.1
    htop pair.top_border pair.raw ht rfl hb pair.target_plain pair.target_pos pair.target_source
    pair.target_exclusive
  have hkey : pair.part.1.getD pair.raw.1 0 = oi := by
    simp only [List.getD_eq_getElem?_getD, pair.owner_pos, Option.getD_some]
  change Disjoint (frameRect execution.params cg pair.run pair.targetPos)
    (installedCaptionSize execution (pair.part.1.getD pair.raw.1 0) pair.raw.2) at hclear
  rw [hkey, hc.2] at hclear
  rw [pair.label_rect, pair.box_rect]
  apply caption_gap_of_disjoint
  unfold r7SelectedTransport
  exact disjoint_sceneTransport (not_meetsInterior_shiftRect
    ((Disjoint.comm _ _).mp hclear))

private theorem installed_group_source {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) :
    pair.topNode.decl = oi ∧ pair.topNode.clusterPath.contains pair.topNode.decl = true ∧
      oi < inp.boxes.length ∧ execution.graph.nodes[oi]? = some pair.topNode := by
  have hc := pair.top_eq
  rw [captionRun_nodes pair.run_eq] at hc
  have hmap : (componentCandidateR pair.spec execution.graph pair.part.1 pair.candidate).nodes =
      (componentGraph execution.graph pair.part.1).nodes := by
    cases pair.spec with
    | none => rw [componentCandidateR_none, componentCandidate_nodes]
    | some spec => rfl
  rw [hmap] at hc
  change (pair.part.1.map (fun key => execution.graph.nodes.getD key default))[pair.raw.1]? =
    some pair.topNode at hc
  simp only [List.getElem?_map, pair.owner_pos, Option.map_some, Option.some.injEq] at hc
  have hlen : oi < execution.graph.nodes.length := by
    by_cases hin : oi < execution.graph.nodes.length
    · exact hin
    · have hnone : execution.graph.nodes[oi]? = none :=
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hin)
      have he : (default : Node) = pair.topNode := by
        simpa only [List.getD_eq_getElem?_getD, hnone, Option.getD_none] using hc
      have hborder := (congrArg Node.border he).trans pair.top_border
      change (0 : Int) = -2 at hborder
      omega
  have hsrc : execution.graph.nodes[oi]? = some pair.topNode := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] at hc
    rw [List.getElem?_eq_getElem hlen, hc]
  have hl0 : oi < execution.graph0.nodes.length := by
    rwa [← exactGraph_length execution.graph_eq]
  have hz : execution.graph0.nodes[oi]? = some execution.graph0.nodes[oi] :=
    List.getElem?_eq_getElem hl0
  obtain ⟨n, hn, hb, hp, hd⟩ := exactGraph_node_key execution.graph_eq hz
  have he : n = pair.topNode := Option.some.inj (hn.symm.trans hsrc)
  have hborder : execution.graph0.nodes[oi].border = -2 := by rw [← hb, he, pair.top_border]
  obtain ⟨hdecl, _, hbox, _, hpath⟩ := measuredGraph_group_origin execution.graph0_eq hz hborder
  have hboxLen := (List.getElem?_eq_some_iff.mp hbox).1
  rw [List.length_map, hdecl] at hboxLen
  rw [he] at hp hd
  exact ⟨hd.trans hdecl, by simp [hp, hd, hpath], hboxLen, hsrc⟩

private theorem installed_raw_y {P : Params} {cg : Graph} {run : Run} {raw : Nat × Rect}
    (h : raw ∈ componentTitles P cg run) :
    raw.2.y = (frameRect P cg run raw.1).y + P.clusterPad := by
  unfold componentTitles at h
  obtain ⟨top, _, hemit⟩ := List.mem_filterMap.mp h
  dsimp only at hemit
  split at hemit
  · contradiction
  · cases hfind : run.proper.nodes.zipIdx.find?
        (fun q => q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
    | none => simp [hfind] at hemit
    | some title =>
      simp [hfind] at hemit
      subst raw
      rfl

private theorem installed_region_title_seed {P : Params} {exact : List Nat}
    {s : RegionSpec} {p : Proper} {i : Nat} {node : Node}
    (hnode : p.nodes[i]? = some ⟨node, false, none, false⟩)
    (hborder : node.border = -2) (halign : p.nodes.length = p.rank.length) :
    ∃ j,
      (coordinateGraphR P exact (some s) p).nodes[j]? =
        some ⟨{ node with border := 3, loopExtent := 0, h := (s.titles.getD node.decl (0, 0)).2 + P.clusterPad }, false, none, false⟩ ∧
      rk (coordinateGraphR P exact (some s) p).rank j =
        rk (coordinateGraphR P exact (some s) p).rank i := by
  let original : ProperNode := ⟨node, false, none, false⟩
  let sized := sizeProperPortsX P exact p
  let tops := titleNodes sized
  let titled := titleReservationsR s.titles P.clusterPad sized
  let copy : ProperNode :=
    ⟨{ node with border := 3, loopExtent := 0, h := (s.titles.getD node.decl (0, 0)).2 + P.clusterPad }, false, none, false⟩
  have hsz : sized.nodes[i]? = some original := by
    have hne : (node.border != 0) = true := by rw [hborder]; decide
    simp only [sized, sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hnode,
      Option.map_some]
    simp [original, hne]
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp
    (show (original, i) ∈ tops from List.mem_filter.mpr
      ⟨List.mem_zipIdx_iff_getElem?.mpr hsz, by simp [original, hborder]⟩)
  let j := p.nodes.length + n
  have htitle : titled.nodes[j]? = some copy := by
    let titleCopy (q : ProperNode × Nat) : ProperNode :=
      { q.1 with
        node := { q.1.node with
          border := 3
          loopExtent := 0
          h := (s.titles.getD q.1.node.decl (0, 0)).2 + P.clusterPad } }
    change (sized.nodes.map titleF ++ tops.map titleCopy)[j]? = some copy
    have hsized_len : sized.nodes.length = p.nodes.length := by
      dsimp [sized]
      exact sizeProperPortsX_length P exact p
    have hle : (sized.nodes.map titleF).length ≤ j := by
      rw [List.length_map, hsized_len]
      exact Nat.le_add_right _ _
    rw [List.getElem?_append_right hle]
    have hindex : j - (sized.nodes.map titleF).length = n := by
      change p.nodes.length + n - (sized.nodes.map titleF).length = n
      rw [List.length_map, hsized_len]
      exact Nat.add_sub_cancel_left _ _
    rw [hindex, List.getElem?_map, hn, Option.map_some]
  obtain ⟨extra, he, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  let bordered := OrderImpl.addClusterBorders titled P.clusterBorderW
  have hb : bordered.nodes[j]? = some copy := by
    change (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[j]? = some copy
    rw [he, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents bordered).nodes[j]? = some copy := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hb] <;> rfl
  have hmat : (materializeDummyPaths (clearProxyExtents bordered)).nodes[j]? =
      some copy := by
    simp [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx, hclear, copy]
  refine ⟨j, hmat, ?_⟩
  obtain ⟨extraRanks, hrank⟩ := addClusterBorders_rank_prefix titled P.clusterBorderW
  have htitleRank : titled.rank = p.rank ++ tops.map (fun q => rk p.rank q.2) := rfl
  change rk (OrderImpl.addClusterBorders titled P.clusterBorderW).rank j =
    rk (OrderImpl.addClusterBorders titled P.clusterBorderW).rank i
  have hin : i < p.rank.length := by
    rw [← halign]
    exact (List.getElem?_eq_some_iff.mp hnode).1
  have hj : j < (p.rank ++ tops.map (fun q => rk p.rank q.2)).length := by
    rw [List.length_append, List.length_map, ← halign]
    exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.mp hn).1 _
  have hii : i < (p.rank ++ tops.map (fun q => rk p.rank q.2)).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hin (Nat.le_add_right _ _)
  have hle : p.rank.length ≤ j := by rw [← halign]; exact Nat.le_add_right _ _
  have hoffset : j - p.rank.length = n := by
    rw [← halign]
    exact Nat.add_sub_cancel_left _ _
  rw [hrank, htitleRank, NormalizeImpl.rk_append_left hj, NormalizeImpl.rk_append_left hii,
    NormalizeImpl.rk_append_right hle, hoffset, NormalizeImpl.rk_append_left hin]
  simp only [rk, List.getD_eq_getElem?_getD, List.getElem?_map, hn, Option.map_some,
    Option.getD_some]

private theorem installed_port_fold {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {jobs : List (RegionCluster × Nat)}
    {start finish : List Int × Array ProperNode}
    (h : jobs.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        pure (x, acc.2.set! c.top { top with node := { top.node with
          h := max (RouteImpl.nodeH pl.p c.top) footprint } })) start = .ok finish)
    {j : Nat} {seed prior : ProperNode}
    (hseed : pl.p.nodes[j]? = some seed) (hprior : start.2[j]? = some prior)
    (hb : prior.node.border = seed.node.border) (hp : prior.node.clusterPath = seed.node.clusterPath)
    (hh : seed.node.h ≤ prior.node.h) :
    ∃ after, finish.2[j]? = some after ∧ after.node.border = seed.node.border ∧
      after.node.clusterPath = seed.node.clusterPath ∧ seed.node.h ≤ after.node.h := by
  induction jobs generalizing start prior with
  | nil =>
    have he : start = finish := Except.ok.inj h
    exact ⟨prior, he ▸ hprior, hb, hp, hh⟩
  | cons job jobs ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hstep, hrest⟩ := bind_ok h
    dsimp only at hstep
    split at hstep
    · simp at hstep
    · obtain ⟨_, _, hstep⟩ := bind_ok hstep
      obtain ⟨_, _, hstep⟩ := bind_ok hstep
      have hmid := (congrArg Prod.snd (Except.ok.inj hstep)).symm
      dsimp only at hmid
      by_cases he : job.1.top = j
      · have hd : start.2.getD j default = prior := by
          simp only [Array.getD_eq_getD_getElem?, hprior, Option.getD_some]
        rw [he, hd, Array.set!_eq_setIfInBounds] at hmid
        let next := { prior with node := { prior.node with
          h := max (RouteImpl.nodeH pl.p j)
            (max job.1.titleH (Loops.requiredHeight cg.slot
              (loopSizes cg.edges labels job.1.node cg.slot))) } }
        have hnext : mid.2[j]? = some next := by
          rw [hmid, Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hprior).1]
        have hheight : seed.node.h ≤ next.node.h := by
          change seed.node.h ≤ max (RouteImpl.nodeH pl.p j) _
          simp only [RouteImpl.nodeH, hseed]
          exact Int.le_max_left _ _
        exact ih hrest hnext hb hp hheight
      · have hnext : mid.2[j]? = some prior := by
          rw [hmid, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne he]
          exact hprior
        exact ih hrest hnext hb hp hh

private theorem installed_cross_title {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok (xs, pinned, reserved, placed))
    {j : Nat} {seed : ProperNode} (hseed : p.nodes[j]? = some seed) :
    placed.rank = p.rank ∧ ∃ after, placed.nodes[j]? = some after ∧
      after.node.border = seed.node.border ∧ after.node.clusterPath = seed.node.clusterPath ∧
      seed.node.h ≤ after.node.h := by
  unfold crossCoordsR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp [bind, Except.bind] at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
    obtain ⟨port, hport, h⟩ := bind_ok h
    have he : placed = port.2 := (congrArg
      (fun q : List Int × List (List Nat) × List (Option Int) × Proper => q.2.2.2)
      (Except.ok.inj h)).symm
    rw [he]
    unfold reservedPortsR at hport
    obtain ⟨finish, hfold, hout⟩ := bind_ok hport
    rw [← Except.ok.inj hout]
    have hstart : p.nodes.toArray[j]? = some seed := by rwa [List.getElem?_toArray]
    obtain ⟨nd, hn, hb, hp, hh⟩ := installed_port_fold hfold hseed hstart rfl rfl (Int.le_refl _)
    exact ⟨rfl, nd, by rwa [Array.getElem?_toList], hb, hp, hh⟩

private theorem installed_spec_height {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec) (hoi : oi < inp.boxes.length) :
    (spec.titles.getD oi (0, 0)).2 =
      (titleCaptionSize execution.params o (execution.lines.getD oi [])).h := by
  obtain ⟨rs, _, heff⟩ := pair.effective_eq
  rw [hs] at heff
  cases rs with
  | none => cases heff
  | some regions =>
    change some spec = r7Spec idSets o execution.params execution.lines at heff
    unfold r7Spec at heff
    split at heff
    · cases heff
    · cases heff
      have hlen : execution.lines.length = inp.boxes.length := by
        have h := execution.lines_eq
        unfold boxLines at h
        exact (mapM_getElem? _ _ _ h).1.trans List.length_zipIdx
      have hbound : oi < execution.lines.length := hlen.symm ▸ hoi
      have hlookup := List.getElem?_eq_getElem hbound
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hlookup, Option.map_some,
        Option.getD_some, titleCaptionSize]
      cases o.direction <;> rfl

private theorem installed_active_caption_bottom {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec) :
    let r := (rk pair.run.proper.rank pair.raw.1).toNat
    ∃ layer, pair.run.layers[r]? = some layer ∧
      pair.raw.2.y + (titleCaptionSize execution.params o (execution.lines.getD oi [])).h ≤
        pair.run.top.getD r 0 + CoordsImpl.layerHeight pair.run.coordinateProper layer := by
  dsimp only
  obtain ⟨hdecl, hpath, hoi, _⟩ := installed_group_source pair
  obtain ⟨_, _, _, _, labeled, pCoord, _, _, _, _, placed, _, yt, ysMid, stages⟩ :=
    componentRunR_stages pair.run_eq
  obtain ⟨y, top⟩ := yt
  have hlabeled := addLabelNodes_untouched_node stages.hLabels
    (normalize_node_record stages.hNorm pair.top_eq) (by rfl)
  have halign : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length stages.hLabels, (Labels.addLabelNodes_metadata stages.hLabels).2.1]
    exact (normalize_node_rank_alignment stages.hNorm).1
  obtain ⟨j, hj, hjRank⟩ := installed_region_title_seed (P := execution.params)
    (exact := exactDecls exactIds inp) (s := spec) hlabeled pair.top_border halign
  have hcoord := stages.hCoord
  rw [hs] at hcoord
  rw [hcoord] at hj hjRank
  obtain ⟨hrank, nd, hnd, hb, hp, hh⟩ :
      placed.rank = pCoord.rank ∧ ∃ nd, placed.nodes[j]? = some nd ∧
        nd.node.border = 3 ∧ nd.node.clusterPath = pair.topNode.clusterPath ∧
        (spec.titles.getD pair.topNode.decl (0, 0)).2 + execution.params.clusterPad ≤ nd.node.h := by
    rcases stages.hPlaced with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, hcross⟩
    · rw [he]
      exact ⟨rfl, _, hj, rfl, rfl, Int.le_refl _⟩
    · exact installed_cross_title hcross hj
  have hfRank : pair.run.proper.rank = placed.rank := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel stages.hProxy).2.1
  have hnonproxy : ¬ (nd.node.border = -2 ∨ nd.node.border = 2) := by simp [hb]
  have hproper : pair.run.proper.nodes[j]? = some nd := by
    rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
    exact ((proxyWidths_rel stages.hProxy).2.2.2.2.2 j nd hnd hnonproxy).1
  have hlayers : RouteImpl.layersOk pair.run.proper pair.run.layers = true := by
    rcases stages.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
    · exact (RouteImpl.routeWithLanes_geometry hlanes).1
    · obtain ⟨_, hbase, _, _⟩ := routeWithLanesR_spec hlanes
      exact (RouteImpl.route_spec hbase).1
  obtain ⟨layer, hly, hmem, hnn⟩ := (RouteImpl.layersOk_spec hlayers).2.2.2.1 j
    (List.getElem?_eq_some_iff.mp hproper).1
  let r := (rk pair.run.proper.rank pair.raw.1).toNat
  have hr : rk pair.run.proper.rank j = rk pair.run.proper.rank pair.raw.1 := by
    rwa [hfRank, hrank]
  have hrj : (rk pair.run.proper.rank j).toNat = r := congrArg Int.toNat hr
  have hly' : pair.run.layers[r]? = some layer := by rwa [hrj] at hly
  have hrc : rk placed.rank j = (r : Int) := by
    rw [← hfRank, ← hrj]
    exact (Int.toNat_of_nonneg hnn).symm
  have hlen := (List.getElem?_eq_some_iff.mp hnd).1
  obtain ⟨_, hmax⟩ := rankAxis_node_in_band stages.hYt hly' hmem hlen hrc
  have hheight : CoordsImpl.nodeH placed j = nd.node.h := by simp only [CoordsImpl.nodeH, hnd]
  rw [hheight] at hmax
  obtain ⟨_, shifts, _, _, _, _, hshift, hyShift⟩ :=
    (runHooksShift_exact execution.params exactIds inp pair.cg execution.measured).shifts
      placed pair.run.layers ysMid top pair.run.ys pair.run.top stages.hReserve
  obtain ⟨hylen, htoplen⟩ := CoordsImpl.rankCoordsWith_length stages.hYt
  have hyMidLen : ysMid.length = placed.nodes.length := by
    rw [← stages.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hylen
  have hproxyY : ysMid.getD j 0 = y.getD j 0 := by
    rw [← stages.hYsMid, proxyYs_getD _ _ _ _ hnd (by rwa [hylen])]
    simp [hb]
  have hys := hyShift j (by rwa [hyMidLen])
  change pair.run.ys.getD j 0 = ysMid.getD j 0 + shifts.getD (rk placed.rank j).toNat 0 at hys
  rw [hproxyY, hrc, Int.toNat_natCast] at hys
  have htop := hshift r (htoplen.symm ▸ (List.getElem?_eq_some_iff.mp hly').1)
  have hget : pair.cg.nodes.getD pair.raw.1 default = pair.topNode := by
    simp only [List.getD_eq_getElem?_getD, pair.top_eq, Option.getD_some]
  have hb' : (pair.cg.nodes.getD pair.raw.1 default).border = -2 := by
    rw [hget]
    exact pair.top_border
  have hmember : nd.node.clusterPath.contains (pair.cg.nodes.getD pair.raw.1 default).decl = true := by
    rw [hget, hp]
    exact hpath
  have hmemberMem : (nd, j) ∈ pair.run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hproper
  have hY := (frameRect_member_vertical (P := execution.params) hb' hmemberMem hmember).1
  change (frameRect execution.params pair.cg pair.run pair.raw.1).y ≤
    pair.run.ys.getD j 0 at hY
  have hrawY := installed_raw_y pair.top_mem
  rw [hdecl, installed_spec_height pair hs hoi] at hh
  refine ⟨layer, hly', ?_⟩
  rw [stages.hCoordProper, htop]
  omega

theorem r7Caption_installed_active_later_rank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hr : (rk pair.run.proper.rank pair.raw.1).toNat <
      (rk pair.run.proper.rank pair.targetPos).toNat) :
    R7_OverlapRowsXGap l.rect b.rect := by
  obtain ⟨capLayer, hcapLayer, hcap⟩ := installed_active_caption_bottom pair hs
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands (exactIds := exactIds) pair.run_eq
  obtain ⟨_, ht, _, hlo, _⟩ := hband pair.target_eq pair.target_plain
  have hy := Int.le_trans hcap (Int.le_trans (hsep hr hcapLayer ht) hlo)
  have hclear : Disjoint (installedCaptionSize execution oi pair.raw.2)
      (frameRect execution.params pair.cg pair.run pair.targetPos) :=
    rect_disjoint_of_y (Or.inl hy)
  rw [pair.label_rect, pair.box_rect]
  apply caption_gap_of_disjoint
  unfold r7SelectedTransport
  exact disjoint_sceneTransport (not_meetsInterior_shiftRect hclear)

private theorem installed_original_rank_nonneg {P : Params} {exact : List Nat} {inp : Input}
    {spec : Option RegionSpec} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {options : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels options = .ok (cg', run))
    {i : Nat} (hi : i < cg'.nodes.length) : 0 ≤ rk run.proper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
    rcases stages.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
    · exact (RouteImpl.routeWithLanes_geometry hlanes).1
    · obtain ⟨_, hbase, _, _⟩ := routeWithLanesR_spec hlanes
      exact (RouteImpl.route_spec hbase).1
  obtain ⟨_, _, _, hnonneg⟩ := (RouteImpl.layersOk_spec hlayers).2.2.2.1 i
    (componentRunR_original_nodes_covered hrun i hi)
  exact hnonneg

private theorem installed_member_rank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hinside : pair.targetNode.clusterPath.contains pair.topNode.decl = true) :
    (rk pair.run.proper.rank pair.raw.1).toNat <
      (rk pair.run.proper.rank pair.targetPos).toNat := by
  let cg := componentCandidateR pair.spec execution.graph pair.part.1 pair.candidate
  have hrun : componentRunR execution.params (exactDecls exactIds inp) pair.spec inp cg
      execution.measured (candidateOrder pair.candidate) = .ok (pair.cg, pair.run) :=
    pair.run_eq
  have hnodes : pair.cg.nodes = cg.nodes := captionRun_nodes hrun
  have hnodesX : cg.nodes = (componentCandidate execution.graph pair.part.1 pair.candidate).nodes := by
    dsimp only [cg]
    rw [hs, componentCandidate_nodes] <;> rfl
  have hpart := (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem (List.mem_of_getElem? hpart)
  obtain ⟨_, _, _, hg⟩ := installed_group_source pair
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlineLen : execution.lines.length = inp.boxes.length :=
    (mapM_getElem? _ _ _ hlines).1.trans List.length_zipIdx
  have hglobalTop : (pair.topNode, oi) ∈ execution.graph.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hg
  obtain ⟨bottom, hbottom⟩ := X_candidate_group_bottom_find execution.graph0_eq execution.graph_eq
    hlineLen hcomp pair.candidate hglobalTop (List.mem_of_getElem? pair.owner_pos) pair.top_border
  have hbot : cg.nodes.zipIdx.find? (fun q =>
      q.1.border == 2 && q.1.decl == pair.topNode.decl) = some bottom := by
    rw [hnodesX]
    exact hbottom
  have houtTop := pair.top_eq
  have houtTarget := pair.target_eq
  rw [hnodes] at houtTop houtTarget
  have htopMem : (pair.topNode, pair.raw.1) ∈ cg.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr houtTop
  have htargetMem : (pair.targetNode, pair.targetPos) ∈ cg.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr houtTarget
  have hconstraint : (⟨pair.raw.1, pair.targetPos, 1, 0, false⟩ : Edge) ∈
      Compound.constraints cg :=
    (compound_member_constraint_edges htopMem pair.top_border hbot htargetMem
      pair.target_plain hinside).1
  have htop := (List.getElem?_eq_some_iff.mp houtTop).1
  have htarget := (List.getElem?_eq_some_iff.mp houtTarget).1
  have hforward := componentRunR_compound_feasible hrun hconstraint htop htarget
  change (1 : Int) ≤ rk pair.run.proper.rank pair.targetPos -
    rk pair.run.proper.rank pair.raw.1 at hforward
  have hnonneg := installed_original_rank_nonneg hrun (List.getElem?_eq_some_iff.mp pair.top_eq).1
  have hlt : rk pair.run.proper.rank pair.raw.1 < rk pair.run.proper.rank pair.targetPos := by
    omega
  exact (Int.toNat_lt_toNat (Int.lt_of_le_of_lt hnonneg hlt)).2 hlt

theorem r7Caption_installed_active_member {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hinside : pair.targetNode.clusterPath.contains pair.topNode.decl = true) :
    R7_OverlapRowsXGap l.rect b.rect :=
  r7Caption_installed_active_later_rank pair hs (installed_member_rank pair hs hinside)

theorem r7Caption_installed_clear_or_remaining {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {l : SceneLabel} {b : Box} {i oi : Nat} {source : ModelLabel}
    (hl : l ∈ res.scene.labels) (hex : b.exclusive = true)
    (hi : inp.labels[i]? = some source) (hid : l.id = source.id)
    (hm : execution.measured.find? (fun item => item.index == i) = none)
    (ho : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi)
    (ht : ((sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
      (fun title => title.1 == source.owner)).isSome = true)
    (hshared : R7_CaptionSharesPart execution oi b) :
    R7_OverlapRowsXGap l.rect b.rect ∨
      (idSets ≠ [] ∧ ∃ pair : R7_InstalledCaptionPair execution oi l b,
        pair.spec = none ∨ (∃ spec, pair.spec = some spec ∧
          pair.targetNode.clusterPath.contains pair.topNode.decl = false ∧
          (rk pair.run.proper.rank pair.targetPos).toNat ≤ (rk pair.run.proper.rank pair.raw.1).toNat)) := by
  obtain ⟨pair⟩ := r7Caption_installed_selectedPair execution hwf hl hex hi hid hm ho ht hshared
  by_cases hempty : idSets = []
  · subst idSets
    exact Or.inl (r7Caption_installed_no_regions execution hwf hfp pair)
  cases hs : pair.spec with
  | none => exact Or.inr ⟨hempty, pair, Or.inl hs⟩
  | some spec =>
    by_cases hlt : (rk pair.run.proper.rank pair.raw.1).toNat <
        (rk pair.run.proper.rank pair.targetPos).toNat
    · exact Or.inl (r7Caption_installed_active_later_rank pair hs hlt)
    · cases hp : pair.targetNode.clusterPath.contains pair.topNode.decl with
      | true => exact Or.inl (r7Caption_installed_active_member pair hs hp)
      | false => exact Or.inr ⟨hempty, pair, Or.inr ⟨spec, hs, hp, by omega⟩⟩

def R7_SelectedCaptionAfterInstalledResidual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (index oi : Nat) (source : ModelLabel),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ source.owner :: res.scene.layoutDump.ancestors source.owner →
    inp.labels[index]? = some source → l.id = source.id →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi →
    max l.rect.y b.rect.y < min (l.rect.y + l.rect.h) (b.rect.y + b.rect.h) →
    0 < l.rect.w → 0 < b.rect.w →
    (let title := (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun row => row.1 == source.owner)
     title.isSome = true ∧ R7_CaptionSharesPart execution oi b ∧ idSets ≠ [] ∧
       ∃ pair : R7_InstalledCaptionPair execution oi l b,
         pair.spec = none ∨ (∃ spec, pair.spec = some spec ∧
           pair.targetNode.clusterPath.contains pair.topNode.decl = false ∧
           (rk pair.run.proper.rank pair.targetPos).toNat ≤
             (rk pair.run.proper.rank pair.raw.1).toNat)) →
    l.rect.x + l.rect.w ≤ b.rect.x ∨ b.rect.x + b.rect.w ≤ l.rect.x

theorem r7Caption_afterDemotedResidual_iff_afterInstalled {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) (hfit : InputFixedFit inp o) :
    R7_SelectedCaptionAfterDemotedResidual execution ↔
      R7_SelectedCaptionAfterInstalledResidual execution := by
  constructor
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    apply h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
    obtain ⟨ht, hshared, _⟩ := hcase
    exact Or.inl ⟨ht, hshared⟩
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    rcases hcase with ⟨ht, hshared⟩ | ⟨ht, _, hactive, _⟩
    · rcases r7Caption_installed_clear_or_remaining execution hwf hfp hl hex hi hid hm ho
        ht hshared with hclear | hremaining
      · exact hclear hrows hlw hbw
      · exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
          ⟨ht, hshared, hremaining⟩
    · exact r7Caption_activeFallback_clear execution hwf hfit hl hex hi hid hm ho ht
        hactive hrows hlw hbw

theorem flatC7B_layoutRIds_reindex_iff_captionAfterInstalled (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC7B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      (∀ (inp : Input) (o : Options) (res : FamilyResult),
        WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
        Elegant.Layered.PartsSeparated inp o res → LabelRunsClearExclusiveBoxes inp o res →
        SceneCaptionBoxContainment inp o res →
        layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
        ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
          R7_SelectedRouteWithPlainTarget execution ∧ R7_SelectedCaptionAfterInstalledResidual execution) := by
  refine (flatC7B_layoutRIds_reindex_iff_captionAfterDemoted exactIds idSets).trans ?_
  constructor
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hroute,
      (r7Caption_afterDemotedResidual_iff_afterInstalled execution hwf hfp hfit).mp hcaption⟩
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hroute,
      (r7Caption_afterDemotedResidual_iff_afterInstalled execution hwf hfp hfit).mpr hcaption⟩


end Elegant.Layered.PipelineImpl
