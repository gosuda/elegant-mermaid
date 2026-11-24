import Elegant.Layered.RegionC7InactiveCaption
import Elegant.Layered.RegionC5ActiveSelected
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.RegionC5ContributorRank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem captionRun_member_band_lower {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions =
      .ok (cg', run)) {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd) :
    let r := (rk run.proper.rank v).toNat
    ∃ layer, run.layers[r]? = some layer ∧ run.top.getD r 0 ≤ run.ys.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, placed, proxied, ⟨y, top⟩, ysMid, hs⟩ :=
    componentRunR_stages hrun
  have hlayers : RouteImpl.layersOk run.proper run.layers = true := by
    rcases hs.hLanes with ⟨_, hlanes⟩ | ⟨_, hlanes⟩
    · exact (RouteImpl.routeWithLanes_geometry hlanes).1
    · obtain ⟨_, hbase, _, _⟩ := routeWithLanesR_spec hlanes
      exact (RouteImpl.route_spec hbase).1
  have hvP := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨layer, hlayer, hmem, hnonneg⟩ := (RouteImpl.layersOk_spec hlayers).2.2.2.1 v hvP
  let r := (rk run.proper.rank v).toNat
  have hrank : run.proper.rank = placed.rank := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_rank]
    exact (proxyWidths_rel hs.hProxy).2.1
  have hnodes : run.proper.nodes = proxied.nodes := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  have hvC : v < placed.nodes.length := by
    rwa [hnodes, (proxyWidths_rel hs.hProxy).2.2.1] at hvP
  have hvPlaced : placed.nodes[v]? = some placed.nodes[v] := List.getElem?_eq_getElem hvC
  obtain ⟨hyLen, htopLen⟩ := CoordsImpl.rankCoordsWith_length hs.hYt
  have hvY : v < y.length := by rwa [hyLen]
  have hrTop : r < top.length := by
    rw [htopLen]
    exact (List.getElem?_eq_some_iff.mp hlayer).1
  have hr : rk placed.rank v = (r : Int) := by
    rw [← hrank]
    exact (Int.toNat_of_nonneg hnonneg).symm
  have hbefore := proxyYs_getD placed run.layers top y hvPlaced hvY
  have hrIdx : (rk placed.rank v).toNat = r := by rw [← hrank] <;> rfl
  have hlo := (rankAxis_node_in_band (r := r) hs.hYt hlayer hmem hvC hr).1
  have hh := CoordsImpl.layerHeight_nonneg placed (run.layers.getD r [])
  simp only [hrIdx] at hbefore
  have hmid : top.getD r 0 ≤ ysMid.getD v 0 := by
    rw [← hs.hYsMid, hbefore]
    split
    · exact Int.le_refl _
    · split
      · omega
      · exact hlo
  have hmidLen : ysMid.length = placed.nodes.length := by
    rw [← hs.hYsMid]
    simpa only [proxyYs, List.length_map, List.length_zipIdx] using hyLen
  obtain ⟨_, shifts, _, _, _, _, htopShift, hyShift⟩ :=
    (runHooksShift_exact P exactIds inp cg' labels).shifts placed run.layers ysMid top
      run.ys run.top hs.hReserve
  have hys := hyShift v (by rwa [hmidLen])
  change run.ys.getD v 0 = ysMid.getD v 0 + shifts.getD (rk placed.rank v).toNat 0 at hys
  rw [hrIdx] at hys
  refine ⟨layer, hlayer, ?_⟩
  change run.top.getD r 0 ≤ run.ys.getD v 0
  rw [htopShift r hrTop, hys]
  exact Int.add_le_add_right hmid _

private theorem captionRaw_y {P : Params} {cg : Graph} {run : Run} {raw : Nat × Rect}
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

private theorem captionMemberHull_nonempty {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec) : groupMemberRects pair.cg pair.run pair.topNode.decl ≠ [] := by
  obtain ⟨rs, hrs, heff⟩ := pair.effective_eq
  have hresolve := componentTrialR_selected_regions pair.candidate hrs
  change newComponentRegions (r7Eff idSets o execution.params execution.lines rs)
    execution.params inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph pair.part.1 pair.candidate) = .ok rs at hresolve
  rw [← heff, hs] at hresolve
  have hsome : ∃ rm, rs = some rm := by
    cases rs with
    | none => rw [hs] at heff; simp [r7Eff] at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hresolve
  have hrun := pair.run_eq
  rw [hs] at hrun
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hresolve
  have htop : (componentCandidate execution.graph pair.part.1 pair.candidate).nodes[pair.raw.1]? =
      some pair.topNode := by
    rw [componentCandidate_nodes]
    have h := pair.top_eq
    rw [rankEquivalentR_nodes_eq hrank] at h
    exact h
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq htop pair.top_border
  obtain ⟨_, actual, _, ha, _, _, _, _, _, hap, _⟩ :=
    componentRunR_active_marker_records hrun hresolve pair.top_eq (Or.inl pair.top_border)
  have hmember : actual.node.clusterPath.contains pair.topNode.decl = true := by
    rw [hap, hpath]
    exact List.contains_iff_mem.mpr (by simp)
  have hm := fbs_groupMemberRects_mem (cg := pair.cg) ha hmember
  intro hempty
  exact List.not_mem_nil (hempty ▸ hm)

/-- A strictly earlier box clears the caption unless a proper member of
the caption frame occurs no later than the box. The witness comes from the
member filter that defines the frame top. -/
theorem r7Caption_installed_active_earlier_clear_or_member {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hearlier : (rk pair.run.proper.rank pair.targetPos).toNat <
      (rk pair.run.proper.rank pair.raw.1).toNat) :
    R7_OverlapRowsXGap l.rect b.rect ∨
      ∃ v nd, pair.run.proper.nodes[v]? = some nd ∧
        nd.node.clusterPath.contains pair.topNode.decl = true ∧
        (rk pair.run.proper.rank v).toNat ≤ (rk pair.run.proper.rank pair.targetPos).toNat ∧
        (rk pair.run.proper.rank v).toNat < (rk pair.run.proper.rank pair.raw.1).toNat := by
  classical
  let peer := (rk pair.run.proper.rank pair.targetPos).toNat
  by_cases hbad : ∃ v nd, pair.run.proper.nodes[v]? = some nd ∧
      nd.node.clusterPath.contains pair.topNode.decl = true ∧ (rk pair.run.proper.rank v).toNat ≤ peer
  · obtain ⟨v, nd, hv, hp, hr⟩ := hbad
    exact Or.inr ⟨v, nd, hv, hp, hr, Nat.lt_of_le_of_lt hr hearlier⟩
  left
  let target := frameRect execution.params pair.cg pair.run pair.targetPos
  let capSize := titleCaptionSize execution.params o (execution.lines.getD oi [])
  let cap : Rect := { pair.raw.2 with w := capSize.w, h := capSize.h }
  obtain ⟨hband, hsep⟩ := componentRunR_plain_rank_bands (exactIds := exactIds) pair.run_eq
  obtain ⟨peerLayer, hpLayer, _, _, hpHi⟩ := hband pair.target_eq pair.target_plain
  have hmembers : ∀ r ∈ groupMemberRects pair.cg pair.run pair.topNode.decl,
      target.y + target.h ≤ r.y := by
    intro r hr
    obtain ⟨v, nd, hv, hp, rfl⟩ := fbs_groupMemberRects_spec hr
    have hlt : peer < (rk pair.run.proper.rank v).toNat :=
      Nat.lt_of_not_ge (fun hh => hbad ⟨v, nd, hv, hp, hh⟩)
    obtain ⟨layer, hl, hlo⟩ := captionRun_member_band_lower
      (exactIds := exactIds) pair.run_eq hv
    change target.y + target.h ≤ pair.run.ys.getD v 0
    exact Int.le_trans hpHi (Int.le_trans (hsep hlt hpLayer hl) hlo)
  have hmin := boundsOf_minY_ge_of_all (captionMemberHull_nonempty pair hs) hmembers
  have hframe : target.y + target.h ≤
      (frameRect execution.params pair.cg pair.run pair.raw.1).y := by
    rw [frameRect_group_span pair.top_eq pair.top_border]
    exact hmin
  have hraw := captionRaw_y pair.top_mem
  have hpad := (checkedParams_sizing_nonneg execution.checked).2.1
  have hsepY : target.y + target.h ≤ cap.y := by
    change target.y + target.h ≤ pair.raw.2.y
    omega
  have hclear : Disjoint cap target := rect_disjoint_of_y (Or.inr hsepY)
  have hlb : Disjoint l.rect b.rect := by
    rw [pair.label_rect, pair.box_rect]
    unfold r7SelectedTransport
    exact disjoint_sceneTransport (not_meetsInterior_shiftRect hclear)
  change ¬ l.rect.meetsInterior b.rect at hlb
  unfold R7_OverlapRowsXGap Rect.meetsInterior at *
  intro hy hwL hwB
  omega

/-- This bounds every actual frame contributor, including indices beyond the
ranked graph's node prefix. It composes the executed contributor provenance
with the original compound rank window. -/
theorem r7Caption_installed_active_member_rank_lower {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    {v : Nat} {nd : ProperNode} (hv : pair.run.proper.nodes[v]? = some nd)
    (howner : nd.node.clusterPath.contains pair.topNode.decl = true) :
    rk pair.run.proper.rank pair.raw.1 ≤ rk pair.run.proper.rank v := by
  obtain ⟨rs, hrs, heff⟩ := pair.effective_eq
  have hselected := componentTrialR_selected_regions pair.candidate hrs
  change newComponentRegions (r7Eff idSets o execution.params execution.lines rs)
    execution.params inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph pair.part.1 pair.candidate) = .ok rs at hselected
  rw [← heff, hs] at hselected
  have hsome : ∃ rm, rs = some rm := by
    cases rs with
    | none =>
      rw [hs] at heff
      simp [r7Eff] at heff
    | some rm => exact ⟨rm, rfl⟩
  obtain ⟨rm, hrm⟩ := hsome
  rw [hrm] at hselected
  have hrun := pair.run_eq
  rw [hs] at hrun
  have hpart := (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components execution.graph := by
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem (List.mem_of_getElem? hpart)
  obtain ⟨_, _, _, _, ha, _, hpath, _, hlo, _⟩ :=
    activeFrameContributorRankSources execution hcomp hrun hselected hv howner
  obtain ⟨_, _, _, _, _, _, _, hwindow⟩ :=
    activeCandidateOriginalFrameRankWindow execution hwf hfp hcomp hrun hselected
      pair.top_eq pair.top_border
  exact Int.le_trans (hwindow ha hpath).1 hlo

/-- A strictly earlier target cannot have an actual frame contributor on or
before its rank. No clearance premise is needed to eliminate that witness. -/
theorem r7Caption_installed_active_earlier_member_impossible {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hearlier : (rk pair.run.proper.rank pair.targetPos).toNat <
      (rk pair.run.proper.rank pair.raw.1).toNat)
    {v : Nat} {nd : ProperNode} (hv : pair.run.proper.nodes[v]? = some nd)
    (howner : nd.node.clusterPath.contains pair.topNode.decl = true)
    (hbefore : (rk pair.run.proper.rank v).toNat ≤
      (rk pair.run.proper.rank pair.targetPos).toNat) : False := by
  have hge := r7Caption_installed_active_member_rank_lower hwf hfp pair hs hv howner
  omega

/-- A selected active title clears a target strictly earlier than its frame top. -/
theorem r7Caption_installed_active_earlier_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_InstalledCaptionPair execution oi l b) {spec : RegionSpec}
    (hs : pair.spec = some spec)
    (hearlier : (rk pair.run.proper.rank pair.targetPos).toNat <
      (rk pair.run.proper.rank pair.raw.1).toNat) : R7_OverlapRowsXGap l.rect b.rect := by
  rcases r7Caption_installed_active_earlier_clear_or_member pair hs hearlier with
    hgap | ⟨_, _, hv, hpath, hbefore, _⟩
  · exact hgap
  · exact (r7Caption_installed_active_earlier_member_impossible hwf hfp pair hs hearlier
      hv hpath hbefore).elim

def R7_SelectedCaptionActiveEqualRankResidual {exactIds : List String}
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
       ∃ (pair : R7_InstalledCaptionPair execution oi l b) (spec : RegionSpec),
         pair.spec = some spec ∧ pair.targetNode.clusterPath.contains pair.topNode.decl = false ∧
         (rk pair.run.proper.rank pair.targetPos).toNat =
           (rk pair.run.proper.rank pair.raw.1).toNat) →
    l.rect.x + l.rect.w ≤ b.rect.x ∨ b.rect.x + b.rect.w ≤ l.rect.x

theorem r7Caption_activeResidual_iff_activeEqualRank {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) :
    R7_SelectedCaptionActiveResidual execution ↔
      R7_SelectedCaptionActiveEqualRankResidual execution := by
  constructor
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    obtain ⟨ht, hshared, hsets, pair, spec, hs, hforeign, hequal⟩ := hcase
    exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
      ⟨ht, hshared, hsets, pair, spec, hs, hforeign, by omega⟩
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    obtain ⟨ht, hshared, hsets, pair, spec, hs, hforeign, hle⟩ := hcase
    by_cases hearlier : (rk pair.run.proper.rank pair.targetPos).toNat <
        (rk pair.run.proper.rank pair.raw.1).toNat
    · exact r7Caption_installed_active_earlier_clear hwf hfp pair hs hearlier hrows hlw hbw
    · exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
        ⟨ht, hshared, hsets, pair, spec, hs, hforeign, by omega⟩

end Elegant.Layered.PipelineImpl
