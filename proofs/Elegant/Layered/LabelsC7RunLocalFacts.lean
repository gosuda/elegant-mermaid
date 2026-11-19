import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.CoordGraph
import Elegant.Layered.FrameClearanceSeam

set_option autoImplicit false

namespace Elegant.Layered

open PipelineImpl

/-! Executed coordinate facts needed by the run-local label clearance seam.

`RouteImpl.CoordFacts` is only produced under the `FrameClearance` premise
(`PipelineImpl.coordFacts_of_parts`), which the clause-7 seam does not carry.
The three fields the label branches consume — same-layer pair separation,
rank-band membership, and the rank-step band recurrence — are proved from the
executed coordinate phases alone; `FrameClearance` feeds only the
`top_clear`/`bottom_clear` fields.  `LabelCoordFacts` records exactly that
subset, and `componentRun_labelFacts` discharges it for every successful
`componentRun` by mirroring the transport proof of `coordFacts_of_parts`. -/

/-- The coordinate facts a successful component run provides without any
frame-clearance premise: positive gap and slot, same-layer pair separation of
non-frame nodes, rank-band membership, and the band recurrence. -/
structure LabelCoordFacts (p : Proper) (layers : List (List Nat)) (x y top : List Int)
    (r : Routing) (gap : Int) (rankGap : Nat → Int) (slot : Int) : Prop where
  gap_pos : 1 ≤ gap
  slot_pos : 1 ≤ slot
  separated : ∀ layer ∈ layers, ∀ (i j a b : Nat), i < j → layer[i]? = some a →
    layer[j]? = some b → ¬ RouteImpl.IsFrame p a → ¬ RouteImpl.IsFrame p b →
    (0 < RouteImpl.nodeH p a ∨ 0 < RouteImpl.nodeH p b) →
    RouteImpl.coordSep gap p a b ≤ RouteImpl.xAt x b - RouteImpl.xAt x a
  node_in_band : ∀ (k : Nat) (l : List Nat) (v : Nat), layers[k]? = some l → v ∈ l →
    v < p.nodes.length → rk p.rank v = (k : Int) →
    top.getD k 0 ≤ RouteImpl.yAt y v ∧
      RouteImpl.yAt y v + RouteImpl.nodeH p v ≤ top.getD k 0 + RouteImpl.layerHeight p l
  bands_disjoint : ∀ (r r' : Nat) (lr lr' : List Nat), r < r' → layers[r]? = some lr →
    layers[r']? = some lr' →
    top.getD r 0 + RouteImpl.layerHeight p lr ≤ top.getD r' 0
  frame_flat : ∀ v, RouteImpl.IsFrame p v → RouteImpl.nodeH p v = 0
  band_step : ∀ (k : Nat) (l : List Nat), layers[k]? = some l → k + 1 < layers.length →
    top.getD (k + 1) 0 =
      top.getD k 0 + RouteImpl.layerHeight p l + rankGap k +
        slot * (r.gaps.getD k default).slots

/-- Every successful `componentRun` carries `LabelCoordFacts`: the same-layer
separation, band membership, and band recurrence of `coordFacts_of_parts`,
proved from the executed `crossCoordsClusterWith`/`proxyWidths`/
`routeWithLanes`/`rankCoordsWith` phases without the `FrameClearance` premise
that only feeds `top_clear`/`bottom_clear`. -/
theorem componentRun_labelFacts {P : Params} (hP : P.Valid) {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (_hd : (cg.edges.map (·.decl)).Nodup) (hS : CgShape cg)
    (h : componentRun P cg labels orderOptions = .ok run) :
    LabelCoordFacts run.proper run.layers run.xs run.ys run.top run.lanes.routing
      (min P.nodeGap P.clusterPad)
      (CoordsImpl.rankGapAt P.rankGap run.proper run.layers) P.slot := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, hord, hxs, hprox, hdrop, hr, hroute, hy,
    hys, _⟩ := componentRun_spec h
  obtain ⟨he, _, _, hdummy⟩ := Labels.addLabelNodes_metadata hl
  have hK : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hproper : coordinateGraph P labeled = run.coordinateProper := hc
  have hq : OrderImpl.dropSynthetic q0 = run.proper := hdrop
  have hy' : rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.lanes.routing.gaps.map (·.slots)) = .ok (run.coordinateYs, run.top) := by
    rw [hroute]
    exact hy
  obtain ⟨hg, hrg, hs, hh⟩ := hP
  obtain ⟨hn1, hcp, _, _, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hxs
  obtain ⟨hrE, hrR, hlen, hxlen, hP1, hP2⟩ := proxyWidths_rel hprox
  have hlay := (RouteImpl.routeWithLanes_geometry hr).1
  obtain ⟨_, _, hmem, hcov, _⟩ := RouteImpl.layersOk_spec hlay
  obtain ⟨_, _, hylen, _, _, htop, hyvv⟩ := CoordsImpl.rankCoordsWith_spec hy'
  have hqn : run.proper.nodes = q0.nodes := by rw [← hq]; rfl
  have hqr : run.proper.rank = run.coordinateProper.rank := by rw [← hq]; exact hrR
  have plain : ∀ {v : Nat} {nd : ProperNode}, run.coordinateProper.nodes[v]? = some nd →
      nd.dummy = true → nd.node.border = 0 :=
    fun {v nd} h hd => pc_plain hK (by rw [hproper]; exact h) hd
  have fflat : ∀ {v : Nat} {nd : ProperNode}, run.coordinateProper.nodes[v]? = some nd →
      (nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0 :=
    fun {v nd} h hb => pc_frame_flat (by rw [hproper]; exact h) hb
  have tuniq : ∀ {a b : Nat} {na nb : ProperNode}, run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb → na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b :=
    fun {a b na nb} ha hb h1 h2 hp =>
      pc_title_unique hK hS (by rw [hproper]; exact ha) (by rw [hproper]; exact hb) h1 h2 hp
  have hq_pc : ∀ (v : Nat) (nd' : ProperNode), run.proper.nodes[v]? = some nd' →
      ∃ nd, run.coordinateProper.nodes[v]? = some nd ∧ nd'.dummy = nd.dummy ∧
        nd'.node.border = nd.node.border ∧ nd'.node.h = nd.node.h := by
    intro v nd' h'
    have hv : v < q0.nodes.length := by
      have := (List.getElem?_eq_some_iff.mp h').1
      rw [hqn] at this
      exact this
    have hv' : v < run.coordinateProper.nodes.length := by omega
    obtain ⟨nd, hnd⟩ : ∃ nd, run.coordinateProper.nodes[v]? = some nd :=
      ⟨run.coordinateProper.nodes[v], List.getElem?_eq_getElem hv'⟩
    obtain ⟨nd2, h2, d2, b2, hh2⟩ := hP1 v nd hnd
    rw [hqn] at h'
    rw [h2] at h'
    have := Option.some.inj h'
    subst this
    exact ⟨nd, hnd, d2, b2, hh2⟩
  have hpc_q : ∀ (v : Nat) (nd : ProperNode), run.coordinateProper.nodes[v]? = some nd →
      ∃ nd', run.proper.nodes[v]? = some nd' ∧ nd'.dummy = nd.dummy ∧
        nd'.node.border = nd.node.border ∧ nd'.node.h = nd.node.h := by
    intro v nd hnd
    obtain ⟨nd', h2, d2, b2, hh2⟩ := hP1 v nd hnd
    exact ⟨nd', by rw [hqn]; exact h2, d2, b2, hh2⟩
  have hnodeHq : ∀ v, RouteImpl.nodeH run.proper v = RouteImpl.nodeH q0 v := by
    intro v; unfold RouteImpl.nodeH; rw [hqn]
  have hnodeH : ∀ v, RouteImpl.nodeH run.proper v = RouteImpl.nodeH run.coordinateProper v :=
    fun v => (hnodeHq v).trans (nodeH_proxy hprox v)
  have hnotframe : ∀ (v : Nat) (pa : ProperNode), run.coordinateProper.nodes[v]? = some pa →
      ¬ RouteImpl.IsFrame run.proper v → pa.node.border ≠ -2 ∧ pa.node.border ≠ 2 := by
    intro v pa hpa hnf
    obtain ⟨qa, hqa, hd, hb, _⟩ := hpc_q v pa hpa
    rw [isFrame_iff hqa] at hnf
    refine ⟨fun hb2 => hnf ⟨?_, Or.inl (by rw [hb]; exact hb2)⟩,
      fun hb2 => hnf ⟨?_, Or.inr (by rw [hb]; exact hb2)⟩⟩ <;>
    · rw [hd]
      cases hdm : pa.dummy
      · rfl
      · have := plain hpa hdm
        omega
  have hcylen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hyvv]; simp
  have hflat : ∀ v, RouteImpl.IsFrame run.proper v → RouteImpl.nodeH run.proper v = 0 := by
    intro v hv
    cases hqv : run.proper.nodes[v]? with
    | none => exact absurd hv (not_isFrame_of_none hqv)
    | some qa =>
      rw [isFrame_iff hqv] at hv
      obtain ⟨pa, hpa, hd, hb, hhh⟩ := hq_pc v qa hqv
      have hf := fflat hpa (by rw [← hb]; exact hv.2)
      have hz : RouteImpl.nodeH run.proper v = qa.node.h := by simp [RouteImpl.nodeH, hqv]
      rw [hz, hhh, hf]
  have hLH : ∀ l, RouteImpl.layerHeight run.proper l =
      CoordsImpl.layerHeight run.coordinateProper l := fun l =>
    by
    have hf : RouteImpl.nodeH run.proper = RouteImpl.nodeH run.coordinateProper :=
      funext hnodeH
    simp only [RouteImpl.layerHeight, hf]; rfl
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro layer hl' i j a b hij ha hb hna hnb _
    have hLa : a ∈ layer := List.mem_of_getElem? ha
    have hLb : b ∈ layer := List.mem_of_getElem? hb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl'
    have hav : a < run.coordinateProper.nodes.length := by
      have h1 := (hmem k layer hk a hLa).1
      rw [hqn] at h1
      omega
    have hbv : b < run.coordinateProper.nodes.length := by
      have h1 := (hmem k layer hk b hLb).1
      rw [hqn] at h1
      omega
    obtain ⟨pa, hpa⟩ : ∃ pa, run.coordinateProper.nodes[a]? = some pa :=
      ⟨_, List.getElem?_eq_getElem hav⟩
    obtain ⟨pb, hpb⟩ : ∃ pb, run.coordinateProper.nodes[b]? = some pb :=
      ⟨_, List.getElem?_eq_getElem hbv⟩
    obtain ⟨a1, a2⟩ := hnotframe a pa hpa hna
    obtain ⟨b1, b2⟩ := hnotframe b pb hpb hnb
    have hsep := CoordsImpl.cluster_all_pairs_separated hxs
      (fun a b na nb ha hb h1 h2 hp => tuniq ha hb h1 h2 hp)
      layer hl' i j a b pa pb hij ha hb hpa hpb a1 a2 b1 b2
    obtain ⟨hqa, hxa⟩ := hP2 a pa hpa (by omega)
    obtain ⟨hqb, hxb⟩ := hP2 b pb hpb (by omega)
    have hqa' : run.proper.nodes[a]? = some pa := by rw [hqn]; exact hqa
    have hqb' : run.proper.nodes[b]? = some pb := by rw [hqn]; exact hqb
    have hwa : RouteImpl.nodeW run.proper a = RouteImpl.nodeW run.coordinateProper a := by
      simp only [RouteImpl.nodeW, hqa', hpa]
    have hwb : RouteImpl.nodeW run.proper b = RouteImpl.nodeW run.coordinateProper b := by
      simp only [RouteImpl.nodeW, hqb', hpb]
    have hxa' : RouteImpl.xAt run.xs a = run.coordinateXs.getD a 0 := by
      simp [RouteImpl.xAt, List.getD_eq_getElem?_getD, hxa]
    have hxb' : RouteImpl.xAt run.xs b = run.coordinateXs.getD b 0 := by
      simp [RouteImpl.xAt, List.getD_eq_getElem?_getD, hxb]
    have hga : RouteImpl.nodeW run.coordinateProper a ≤
        CoordsImpl.nodeW run.coordinateProper a := CoordsImpl.nodeW_ge_width _ a
    have hgb : RouteImpl.nodeW run.coordinateProper b ≤
        CoordsImpl.nodeW run.coordinateProper b := CoordsImpl.nodeW_ge_width _ b
    unfold CoordsImpl.coordSep at hsep
    unfold RouteImpl.coordSep
    rw [hxa', hxb', hwa, hwb]
    simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
    omega
  · intro k l v hkl hv hvn hrk
    obtain ⟨qa, hqa⟩ : ∃ qa, run.proper.nodes[v]? = some qa :=
      ⟨_, List.getElem?_eq_getElem hvn⟩
    obtain ⟨pa, hpa, hd, hb, hhh⟩ := hq_pc v qa hqa
    have hvn' : v < run.coordinateProper.nodes.length := by
      have := hvn
      rw [hqn] at this
      omega
    have hv' : v < run.coordinateYs.length := by rw [hcylen]; exact hvn'
    have hrk' : rk run.coordinateProper.rank v = (k : Int) := by rw [← hqr]; exact hrk
    have hLH' := hLH l
    rw [hnodeH v, hLH']
    have hnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper l := by
      rw [← hLH']; exact RouteImpl.layerHeight_nonneg run.proper l
    by_cases h2 : pa.node.border = -2
    · have hyv : RouteImpl.yAt run.ys v = run.top.getD k 0 := by
        rw [← hys]
        unfold RouteImpl.yAt
        rw [proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs hpa hv']
        simp [h2, hrk']
      have hz : RouteImpl.nodeH run.coordinateProper v = 0 := by
        have : RouteImpl.nodeH run.coordinateProper v = pa.node.h := by
          simp [RouteImpl.nodeH, hpa]
        rw [this]; exact fflat hpa (Or.inl h2)
      rw [hyv, hz]
      omega
    · by_cases h3 : pa.node.border = 2
      · have hyv : RouteImpl.yAt run.ys v =
            run.top.getD k 0 + CoordsImpl.layerHeight run.coordinateProper l := by
          rw [← hys]
          unfold RouteImpl.yAt
          rw [proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs hpa hv']
          have hb2 : (pa.node.border == -2) = false := by simpa using h2
          have hb3 : (pa.node.border == 2) = true := by simpa using h3
          simp [hb2, hb3, hrk', List.getD_eq_getElem?_getD, hkl]
        have hz : RouteImpl.nodeH run.coordinateProper v = 0 := by
          have : RouteImpl.nodeH run.coordinateProper v = pa.node.h := by
            simp [RouteImpl.nodeH, hpa]
          rw [this]; exact fflat hpa (Or.inr h3)
        rw [hyv, hz]
        omega
      · have hyv : RouteImpl.yAt run.ys v = run.coordinateYs.getD v 0 := by
          rw [← hys]
          unfold RouteImpl.yAt
          rw [proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs hpa hv']
          have hb2 : (pa.node.border == -2) = false := by simpa using h2
          have hb3 : (pa.node.border == 2) = false := by simpa using h3
          simp [hb2, hb3]
        have hb := CoordsImpl.rankAxis_node_in_band hy' hkl hv hvn' hrk'
        rw [hyv]
        exact hb
  · intro r r' lr lr' hr hrl hrr'
    have hb := CoordsImpl.rankAxis_bands_disjoint hy' r r' lr lr' hr hrl hrr'
    simp only [hLH lr]
    exact hb
  · intro v hv
    exact hflat v hv
  · intro k l hkl hk
    obtain ⟨_, _, _, _, hgl, _, _⟩ := RouteImpl.routeWithLanes_geometry hr
    rw [htop]
    have hk' : k < run.lanes.routing.gaps.length := by omega
    have hh' : (run.layers.map (CoordsImpl.layerHeight run.coordinateProper)).getD k 0 =
        CoordsImpl.layerHeight run.coordinateProper l := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hkl]
    have hs' : (run.lanes.routing.gaps.map (·.slots)).getD k 0 =
        (run.lanes.routing.gaps.getD k default).slots := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk']
    rw [rankSteps_topsFrom_step P.rankGap P.slot run.coordinateProper run.layers
      (run.lanes.routing.gaps.map (·.slots)) 0 k (by simp; omega) (by simpa using hk), hh', hs',
      hLH l]
    rw [show CoordsImpl.rankGapAt P.rankGap run.proper run.layers k =
      CoordsImpl.rankGapAt P.rankGap run.coordinateProper run.layers k by
        rw [← hq]; exact rankGapAt_proxy hprox _ _ _]

/-! ## Structural facts of the executed pipeline -/

/-- Normalization only ever appends chain dummies; every node it leaves with an
edge anchor identity is one of them. -/
private theorem normalizeEdge_edge_dummies {slot : Int} {q q' : Proper} {e : Edge} {idx : Nat}
    (h : NormalizeImpl.normalizeEdge slot q e idx = .ok q')
    (hinv : ∀ nd ∈ q.nodes, nd.edge ≠ none → nd.dummy = true) :
    ∀ nd ∈ q'.nodes, nd.edge ≠ none → nd.dummy = true := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · rename_i heq
    intro nd hnd hedge
    have hinj := Except.ok.inj h
    rw [← hinj] at hnd
    exact hinv nd hnd hedge
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i p1 _ _
        have he := Except.ok.inj h
        subst he
        intro nd hnd hedge
        rcases List.mem_append.mp hnd with hm | hm
        · exact hinv nd hm hedge
        · unfold NormalizeImpl.dummyNodes at hm
          rw [List.mem_replicate] at hm
          obtain ⟨_, heq⟩ := hm
          rw [heq]

private theorem normalizeLoop_edge_dummies (slot : Int) :
    ∀ (l : List (Edge × Nat)) (q q' : Proper),
      (∀ nd ∈ q.nodes, nd.edge ≠ none → nd.dummy = true) →
      NormalizeImpl.normalizeLoop slot l q = .ok q' →
      ∀ nd ∈ q'.nodes, nd.edge ≠ none → nd.dummy = true := by
  intro l
  induction l with
  | nil =>
    intro q q' hinv h
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hinv
  | cons e es ih =>
    intro q q' hinv h
    simp only [NormalizeImpl.normalizeLoop] at h
    split at h
    · simp at h
    · rename_i p1 hp1
      exact ih p1 q' (normalizeEdge_edge_dummies hp1 hinv) h

theorem normalize_edge_dummies {g : Graph} {ranks : List Int} {p : Proper}
    (h : normalize g ranks = .ok p) :
    ∀ nd ∈ p.nodes, nd.edge ≠ none → nd.dummy = true := by
  unfold normalize at h
  split at h
  · simp at h
  · rename_i slot hs
    split at h
    · refine normalizeLoop_edge_dummies slot _ _ _ ?_ h
      intro nd hnd hedge
      rcases List.mem_map.mp hnd with ⟨n, _, rfl⟩
      exact absurd rfl hedge
    · simp at h

/-- The anchor index carries its rank and bounds, read off the `find?`
condition that defines it. -/
theorem labelAnchorIndex_rank {p : Proper} {edge index : Nat} {rank : Int}
    (hi : labelAnchorIndex p edge rank = some index) :
    rk p.rank index = rank ∧ index < p.nodes.length := by
  rw [labelAnchorIndex_eq] at hi
  cases hf : p.nodes.zipIdx.find? (fun q =>
      q.1.edge == some edge && rk p.rank q.2 == rank) with
  | none => simp [hf] at hi
  | some found =>
    simp only [hf, Option.map_some, Option.some.injEq] at hi
    have hmem := List.mem_of_find?_eq_some hf
    have hnd : p.nodes[found.2]? = some found.1 :=
      List.mem_zipIdx_iff_getElem?.mp hmem
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [show found.2 = index from hi ▸ rfl] at hnd hp
    exact ⟨hp.2, (List.getElem?_eq_some_iff.mp hnd).1⟩

end Elegant.Layered
