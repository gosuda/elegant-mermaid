import Elegant.Layered.RegionActualParts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-!
# Region run placement facts.

Proves two of the five open single facts about `componentRunR` stated as
`componentRunR_*_factR` defs in `RegionActualParts.lean`:

* `componentRunR_title_zeroingR`: title-border (`-2`/`2`) nodes of
  `run.coordinateProper` have `w = 0` (full statement, proved).
* `componentRunR_placement_xsR`: placed xs read the coordinate xs at every
  non-title index. The matching `componentRunR_placement_xs_factR` quantifies
  over all indices, but the none-spec probe
  (`wip/Probe/RegionRunPlacementFactsTProbe.lean`) exhibits six title indices
  with `run.xs.getD i 0 ≠ run.coordinateXs.getD i 0`, so the full statement is
  false; this theorem is the strictly narrower residual that the exact twins
  (`X_border_record`, `X_nonproxy_record` in `ExactFlatC2.lean`) also prove.

Both replay the exact runs over `componentRunR`: peel one bind at a time,
`split at h` on the distributed `match`/`if` first, and state the
`congrArg .. he` equations `.symm`.
-/

/-- `titleF` zeroes the width of title-border nodes. -/
private theorem rpf_titleF_w (n : ProperNode)
    (hb : n.node.border = -2 ∨ n.node.border = 2) :
    (titleF n).node.w = 0 := by
  have hc : (n.node.border == -2 || n.node.border == 2) = true := by
    rcases hb with hb | hb <;> simp [hb]
  unfold titleF
  simp [hc]

 /-- `clearF` preserves widths. -/
private theorem rpf_clearF_w (n : ProperNode) : (clearF n).node.w = n.node.w := by
   unfold clearF
   by_cases hc : (n.node.border == -2 || n.node.border == 2) = true
   · simp [hc]
   · simp [hc]

 /-- `materializeDummyPaths` preserves widths and borders. -/
 private theorem rpf_materialize_w (p : Proper) (v : Nat) (nd : ProperNode)
     (h : (materializeDummyPaths p).nodes[v]? = some nd) :
     ∃ m, p.nodes[v]? = some m ∧ nd.node.w = m.node.w ∧
       nd.node.border = m.node.border := by
   unfold materializeDummyPaths at h
   simp only [List.getElem?_map, List.getElem?_zipIdx] at h
   cases hp : p.nodes[v]? with
   | none => simp [hp] at h
   | some m =>
     simp only [hp, Option.map_some, Option.some.injEq] at h
     by_cases hd : m.dummy = true
     · simp only [hd, ↓reduceIte] at h
       subst h
       exact ⟨m, rfl, rfl, rfl⟩
     · have hd' : m.dummy = false := by simpa using hd
       simp only [hd', Bool.false_eq_true, ↓reduceIte] at h
       subst h
       exact ⟨m, rfl, rfl, rfl⟩

 /-- Title-border nodes of the exact title reservation have width zero. -/
 private theorem rpf_titledX_w (P : Params) (exact : List Nat) (p : Proper)
     (v : Nat) (nd : ProperNode)
     (h : (titleReservations (sizeProperPortsX P exact p)).nodes[v]? = some nd)
     (hb : nd.node.border = -2 ∨ nd.node.border = 2) :
     nd.node.w = 0 := by
   rw [titleReservations_nodes] at h
   by_cases hi : v < (sizeProperPortsX P exact p).nodes.length
   · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
       List.getElem?_map] at h
     cases hs : (sizeProperPortsX P exact p).nodes[v]? with
     | none => simp [hs] at h
     | some s =>
       simp only [hs, Option.map_some, Option.some.injEq] at h
       have hbs : s.node.border = -2 ∨ s.node.border = 2 := by
         have hk := (titleF_keys s).2.1
         rw [h] at hk
         omega
       have hw := rpf_titleF_w s hbs
       rw [h] at hw
       exact hw
   · rw [List.getElem?_append_right
       (by simpa only [List.length_map] using Nat.le_of_not_gt hi),
       List.getElem?_map, Option.map_eq_some_iff] at h
     obtain ⟨q, _, heq⟩ := h
     have h3 : (copyF q).node.border = 3 := rfl
     rw [heq] at h3
     omega

 /-- Peel helper (prefixed copy: `bind_ok` is private in every module). -/
 private theorem rpf_bind_ok {α β : Type}
     {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
     (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
   cases x with
   | error e => cases h
   | ok a => exact ⟨a, rfl, h⟩

 /-- Title-border nodes of the region title reservation have width zero. -/
 private theorem rpf_titledR_w (titles : List (Int × Int)) (pad : Int) (p : Proper)
     (v : Nat) (nd : ProperNode)
     (h : (titleReservationsR titles pad p).nodes[v]? = some nd)
     (hb : nd.node.border = -2 ∨ nd.node.border = 2) :
     nd.node.w = 0 := by
   unfold RegionImpl.titleReservationsR at h
   dsimp only at h
   by_cases hi : v < p.nodes.length
   · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
       List.getElem?_map] at h
     cases hs : p.nodes[v]? with
     | none => simp [hs] at h
     | some s =>
         simp only [hs, Option.map_some, Option.some.injEq] at h
         by_cases hc : (s.node.border == -2 || s.node.border == 2) = true
         · simp only [hc, ↓reduceIte] at h
           rw [← h]
         · simp only [hc] at h
           have hb' : s.node.border = -2 ∨ s.node.border = 2 := by
             rw [← h] at hb
             exact hb
           have hcon : (s.node.border == -2 || s.node.border == 2) = true := by
             rcases hb' with hb' | hb' <;> simp [hb']
           exact absurd hcon hc
   · rw [List.getElem?_append_right
       (by simpa only [List.length_map] using Nat.le_of_not_gt hi),
       List.getElem?_map, Option.map_eq_some_iff] at h
     obtain ⟨q, _, heq⟩ := h
     have h3 : nd.node.border = 3 := by rw [← heq]
     omega

 /-- `clearProxyExtents` preserves widths and borders. -/
 private theorem rpf_clearProxy_w (p : Proper) (v : Nat) (nd : ProperNode)
     (h : (clearProxyExtents p).nodes[v]? = some nd) :
     ∃ m, p.nodes[v]? = some m ∧ nd.node.w = m.node.w ∧
       nd.node.border = m.node.border := by
   rw [clearProxyExtents_nodes, List.getElem?_map] at h
   cases hm : p.nodes[v]? with
   | none => simp [hm] at h
   | some m =>
       simp only [hm, Option.map_some, Option.some.injEq] at h
       have hb : nd.node.border = m.node.border := by
         have hk := (clearF_keys m).2.1
         rw [h] at hk
         exact hk
       have hw : nd.node.w = m.node.w := by
         have hw0 := rpf_clearF_w m
         rw [h] at hw0
         exact hw0
       exact ⟨m, rfl, hw, hb⟩

 /-- Appended border pairs never carry a title border, so title nodes survive
 `addClusterBorders` at their existing index with widths intact. -/
 private theorem rpf_addClusterBorders_w (p : Proper) (bw : Int) (v : Nat)
     (nd : ProperNode)
     (h : (OrderImpl.addClusterBorders p bw).nodes[v]? = some nd)
     (hb : nd.node.border = -2 ∨ nd.node.border = 2) :
     ∃ m, p.nodes[v]? = some m ∧ nd.node.w = m.node.w ∧
       nd.node.border = m.node.border := by
   obtain ⟨extra, hx, hmem⟩ := addClusterBorders_extra p bw
   rw [hx] at h
   by_cases hi : v < p.nodes.length
   · rw [List.getElem?_append_left hi] at h
     exact ⟨nd, h, rfl, rfl⟩
   · rw [List.getElem?_append_right (Nat.le_of_not_gt hi)] at h
     have hmem' : nd ∈ extra := List.mem_of_getElem? h
     obtain ⟨_, hbor⟩ := hmem nd hmem'
     omega

 /-- Title-border nodes of either region coordinate graph have width zero. -/
 private theorem rpf_coordGraphR_title_w (P : Params) (exact : List Nat)
     (spec : Option RegionSpec) (labeled : Proper) (v : Nat) (nd : ProperNode)
     (h : (coordinateGraphR P exact spec labeled).nodes[v]? = some nd)
     (hb : nd.node.border = -2 ∨ nd.node.border = 2) :
     nd.node.w = 0 := by
   cases spec with
   | none =>
       rw [coordinateGraphR_none] at h
       unfold coordinateGraphX at h
       obtain ⟨m1, hm1, hw1, hb1⟩ := rpf_materialize_w _ _ _ h
       obtain ⟨m2, hm2, hw2, hb2⟩ := rpf_clearProxy_w _ _ _ hm1
       have hb1' : m1.node.border = -2 ∨ m1.node.border = 2 := by
         rw [← hb1]; exact hb
       have hm2b : m2.node.border = -2 ∨ m2.node.border = 2 := by
         rw [← hb2]; exact hb1'
       obtain ⟨m3, hm3, hw3, hb3⟩ := rpf_addClusterBorders_w _ _ _ _ hm2 hm2b
       have hb3' : m3.node.border = -2 ∨ m3.node.border = 2 := by
         rw [← hb3]; exact hm2b
       have hw := rpf_titledX_w P exact labeled v m3 hm3 hb3'
       rw [hw1, hw2, hw3]; exact hw
   | some s =>
       unfold coordinateGraphR at h
       dsimp only at h
       obtain ⟨m1, hm1, hw1, hb1⟩ := rpf_materialize_w _ _ _ h
       obtain ⟨m2, hm2, hw2, hb2⟩ := rpf_clearProxy_w _ _ _ hm1
       have hb1' : m1.node.border = -2 ∨ m1.node.border = 2 := by
         rw [← hb1]; exact hb
       have hm2b : m2.node.border = -2 ∨ m2.node.border = 2 := by
         rw [← hb2]; exact hb1'
       obtain ⟨m3, hm3, hw3, hb3⟩ := rpf_addClusterBorders_w _ _ _ _ hm2 hm2b
       have hb3' : m3.node.border = -2 ∨ m3.node.border = 2 := by
         rw [← hb3]; exact hm2b
       have hw := rpf_titledR_w s.titles P.clusterPad (sizeProperPortsX P exact labeled)
         v m3 hm3 hb3'
       rw [hw1, hw2, hw3]; exact hw

 /-- The `reservedPortsR` cluster fold only raises top-node heights: widths and
 borders survive every step. -/
 private theorem rpf_reservedPortsR_fold_w (pl : RegionPlacement)
     (cg : Graph) (labels : List MeasuredLabel)
     (l : List (RegionCluster × Nat))
     (x0 : List Int) (arr : Array ProperNode)
     (ih : ∀ (i : Nat) (m' : ProperNode), arr[i]? = some m' →
       ∃ m, pl.p.nodes[i]? = some m ∧ m'.node.w = m.node.w ∧
         m'.node.border = m.node.border)
     (out : List Int × Array ProperNode)
     (h : l.foldlM (fun acc q => do
       let c := q.1
       let footprint := max c.titleH
         (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
       if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
       else
         let x ← clusterPortR pl q.2 c.top acc.1
         let x ← clusterPortR pl q.2 c.bottom x
         let top := acc.2.getD c.top default
         let nodes := acc.2.set! c.top { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
         pure (x, nodes)) (x0, arr) = .ok out) :
     ∀ (i : Nat) (m' : ProperNode), out.2[i]? = some m' →
       ∃ m, pl.p.nodes[i]? = some m ∧ m'.node.w = m.node.w ∧
         m'.node.border = m.node.border := by
   induction l generalizing x0 arr with
   | nil =>
       intro i m' hm'
       simp only [List.foldlM_nil] at h
       have he := Except.ok.inj h
       subst he
       exact ih i m' hm'
   | cons q l ihl =>
       intro i m' hm'
       simp only [List.foldlM_cons] at h
       obtain ⟨mid, hmid, hrest⟩ := rpf_bind_ok h
       split at hmid
       · simp at hmid
       · obtain ⟨x1, _, hmid⟩ := rpf_bind_ok hmid
         obtain ⟨x2, _, hmid⟩ := rpf_bind_ok hmid
         have he := Except.ok.inj hmid
         have hsetW : ∀ (j : Nat) (m'' : ProperNode), mid.2[j]? = some m'' →
             ∃ m, pl.p.nodes[j]? = some m ∧ m''.node.w = m.node.w ∧
               m''.node.border = m.node.border := by
           intro j m'' hm''
           rw [← he] at hm''
           dsimp only at hm''
           rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hm''
           by_cases heq : q.1.top = j
           · subst heq
             rw [ite_eq_left rfl] at hm''
             by_cases hin : q.1.top < arr.size
             · simp only [ite_eq_left hin] at hm''
               have hget : arr[q.1.top]? = some (arr.toList[q.1.top]) := by
                 have hlen : q.1.top < arr.toList.length := by
                   rw [Array.length_toList]; exact hin
                 have hg := List.getElem?_eq_getElem hlen
                 rwa [Array.getElem?_toList] at hg
               obtain ⟨m0, hm0, hw0, hb0⟩ := ih q.1.top _ hget
               refine ⟨m0, hm0, ?_, ?_⟩
               · rw [← Option.some.inj hm'']
                 show (arr.getD q.1.top default).node.w = m0.node.w
                 rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
                 exact hw0
               · rw [← Option.some.inj hm'']
                 show (arr.getD q.1.top default).node.border = m0.node.border
                 rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
                 exact hb0
             · simp only [ite_eq_right hin] at hm''
               simp at hm''
           · simp only [ite_eq_right heq] at hm''
             exact ih j m'' hm''
         have he1 : x2 = mid.1 := congrArg Prod.fst he
         have he2 : (x2, mid.2) = mid := by
           rw [he1]
         rw [← he2] at hrest
         exact ihl x2 mid.2 hsetW hrest i m' hm'

 /-- Title zeroing in the no-region arm: the coordinate graph is used directly. -/
 private theorem rpf_title_noneR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
     {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrs : RegionImpl.newComponentRegions spec P inp cg = .ok none)
     (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
     {n : ProperNode} (hmem : n ∈ run.coordinateProper.nodes)
     (hb : n.node.border = -2 ∨ n.node.border = 2) :
     n.node.w = 0 := by
   unfold componentRunR at h
   obtain ⟨rs, hrs', h⟩ := rpf_bind_ok h
   have hrsEq : rs = none := Except.ok.inj (hrs'.symm.trans hrs)
   subst hrsEq
   dsimp only at h
   obtain ⟨rr, _, h⟩ := rpf_bind_ok h
   obtain ⟨ranked, _, h⟩ := rpf_bind_ok h
   cases ranked with
   | mk ranks rest =>
       cases rest with
       | mk cg1 rankBudget =>
         dsimp only at h
         obtain ⟨p0, _, h⟩ := rpf_bind_ok h
         obtain ⟨p, _, h⟩ := rpf_bind_ok h
         obtain ⟨_, _, h⟩ := rpf_bind_ok h
         obtain ⟨ord, _, h⟩ := rpf_bind_ok h
         obtain ⟨xs, _, h⟩ := rpf_bind_ok h
         obtain ⟨placed, hplaced, h⟩ := rpf_bind_ok h
         obtain ⟨routed, _, h⟩ := rpf_bind_ok h
         have heP := Except.ok.inj hplaced
         have hbase : placed.2.2.snd = coordinateGraphR P exact spec p := by
           rw [← heP]
         split at h
         · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
           obtain ⟨yt, _, h⟩ := rpf_bind_ok h
           obtain ⟨resv, _, h⟩ := rpf_bind_ok h
           obtain ⟨routes, _, h⟩ := rpf_bind_ok h
           have he := Except.ok.inj h
           have hC0 : run.coordinateProper = placed.2.2.snd :=
             (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
           rw [hbase] at hC0
           rw [hC0] at hmem
           obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
           exact rpf_coordGraphR_title_w P exact spec p v n hv hb
         · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
           obtain ⟨yt, _, h⟩ := rpf_bind_ok h
           obtain ⟨resv, _, h⟩ := rpf_bind_ok h
           obtain ⟨routes, _, h⟩ := rpf_bind_ok h
           have he := Except.ok.inj h
           have hC0 : run.coordinateProper = placed.2.2.snd :=
             (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
           rw [hbase] at hC0
           rw [hC0] at hmem
           obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
           exact rpf_coordGraphR_title_w P exact spec p v n hv hb

 /-- `crossCoordsR` only raises top-node heights: the output proper graph keeps
 the input widths and borders at every index. -/
 private theorem rpf_crossCoordsR_w (P : Params) (rm : ComponentRegions)
     (cg : Graph) (labels : List MeasuredLabel) (p : Proper)
     (m : RegionConstraints) (layers : List (List Nat))
     (out : List Int × List (List Nat) × List (Option Int) × Proper)
     (h : crossCoordsR P rm cg labels p m layers = .ok out) :
     ∀ (i : Nat) (n : ProperNode), out.2.2.2.nodes[i]? = some n →
       ∃ m0, p.nodes[i]? = some m0 ∧ n.node.w = m0.node.w ∧
         n.node.border = m0.node.border := by
   unfold crossCoordsR at h
   obtain ⟨children, _, h⟩ := rpf_bind_ok h
   dsimp only at h
   split at h
   · simp only [bind, Except.bind] at h
     exact absurd h (by simp)
   · obtain ⟨ngs, _, h⟩ := rpf_bind_ok h
     obtain ⟨xcr, _, h⟩ := rpf_bind_ok h
     obtain ⟨_, _, h⟩ := rpf_bind_ok h
     obtain ⟨allocx, _, h⟩ := rpf_bind_ok h
     obtain ⟨xp, hxp, h⟩ := rpf_bind_ok h
     have he := Except.ok.inj h
     have hC : out.2.2.2 = xp.2 :=
       (congrArg (fun q : List Int × List (List Nat) × List (Option Int) × Proper =>
         q.2.2.2) he).symm
     unfold reservedPortsR at hxp
     obtain ⟨fout, hfold, h1⟩ := rpf_bind_ok hxp
     have he1 := Except.ok.inj h1
     have hxp2 : xp.2.nodes = fout.2.toList :=
       (congrArg (fun q : List Int × Proper => q.2.nodes) he1).symm
     have hbase : ∀ (j : Nat) (m' : ProperNode), (p.nodes.toArray)[j]? = some m' →
         ∃ m0, p.nodes[j]? = some m0 ∧ m'.node.w = m0.node.w ∧
           m'.node.border = m0.node.border := by
       intro j m' hj
       rw [List.getElem?_toArray] at hj
       exact ⟨m', hj, rfl, rfl⟩
     have hfoldW := rpf_reservedPortsR_fold_w _ cg labels _ _ _ hbase _ hfold
     intro i n hn
     rw [hC, hxp2, Array.getElem?_toList] at hn
     obtain ⟨m0, hm0, hw0, hb0⟩ := hfoldW i n hn
     exact ⟨m0, hm0, hw0, hb0⟩

 /-- Title zeroing in the region arm: widths survive `crossCoordsR`. -/
 private theorem rpf_title_someR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
     {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions} (rm : RegionImpl.ComponentRegions)
     (hrs : RegionImpl.newComponentRegions spec P inp cg = .ok (some rm))
     (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
     {n : ProperNode} (hmem : n ∈ run.coordinateProper.nodes)
     (hb : n.node.border = -2 ∨ n.node.border = 2) :
     n.node.w = 0 := by
   unfold componentRunR at h
   obtain ⟨rs, hrs', h⟩ := rpf_bind_ok h
   have hrsEq : rs = some rm := Except.ok.inj (hrs'.symm.trans hrs)
   subst hrsEq
   dsimp only at h
   obtain ⟨ranked, _, h⟩ := rpf_bind_ok h
   cases ranked with
   | mk ranks rest =>
       cases rest with
       | mk cg1 rankBudget =>
         dsimp only at h
         obtain ⟨p0, _, h⟩ := rpf_bind_ok h
         obtain ⟨p, _, h⟩ := rpf_bind_ok h
         obtain ⟨_, _, h⟩ := rpf_bind_ok h
         obtain ⟨_, _, h⟩ := rpf_bind_ok h
         obtain ⟨ord, _, h⟩ := rpf_bind_ok h
         split at h
         · simp only [bind, Except.bind] at h
           exact absurd h (by simp)
         · obtain ⟨m_wit, _, h⟩ := rpf_bind_ok h
           obtain ⟨placed, hplaced, h⟩ := rpf_bind_ok h
           obtain ⟨routed, _, h⟩ := rpf_bind_ok h
           have hcorr := rpf_crossCoordsR_w _ _ _ _ _ _ _ _ hplaced
           split at h
           · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
             obtain ⟨yt, _, h⟩ := rpf_bind_ok h
             obtain ⟨resv, _, h⟩ := rpf_bind_ok h
             obtain ⟨routes, _, h⟩ := rpf_bind_ok h
             have he := Except.ok.inj h
             have hC0 : run.coordinateProper = placed.2.2.snd :=
               (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
             rw [hC0] at hmem
             obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
             obtain ⟨m, hm, hw, hbnd⟩ := hcorr v n hv
             have hbm : m.node.border = -2 ∨ m.node.border = 2 := by
               rw [← hbnd]; exact hb
             have hw0 := rpf_coordGraphR_title_w P exact spec _ v m hm hbm
             rw [hw]; exact hw0
           · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
             obtain ⟨yt, _, h⟩ := rpf_bind_ok h
             obtain ⟨resv, _, h⟩ := rpf_bind_ok h
             obtain ⟨routes, _, h⟩ := rpf_bind_ok h
             have he := Except.ok.inj h
             have hC0 : run.coordinateProper = placed.2.2.snd :=
               (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
             rw [hC0] at hmem
             obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
             obtain ⟨m, hm, hw, hbnd⟩ := hcorr v n hv
             have hbm : m.node.border = -2 ∨ m.node.border = 2 := by
               rw [← hbnd]; exact hb
             have hw0 := rpf_coordGraphR_title_w P exact spec _ v m hm hbm
             rw [hw]; exact hw0

 /-- Placed xs read the coordinate xs at every non-title index (no-region arm). -/
 private theorem rpf_place_noneR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
     {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
     (hrs : RegionImpl.newComponentRegions spec P inp cg = .ok none)
     (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
     {i : Nat} {n : ProperNode}
     (hnode : run.coordinateProper.nodes[i]? = some n)
     (hnt : ¬ (n.node.border = -2 ∨ n.node.border = 2)) :
     run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
   unfold componentRunR at h
   obtain ⟨rs, hrs', h⟩ := rpf_bind_ok h
   have hrsEq : rs = none := Except.ok.inj (hrs'.symm.trans hrs)
   subst hrsEq
   dsimp only at h
   obtain ⟨rr, _, h⟩ := rpf_bind_ok h
   obtain ⟨ranked, _, h⟩ := rpf_bind_ok h
   cases ranked with
   | mk ranks rest =>
       cases rest with
       | mk cg1 rankBudget =>
         dsimp only at h
         obtain ⟨p0, _, h⟩ := rpf_bind_ok h
         obtain ⟨p, _, h⟩ := rpf_bind_ok h
         obtain ⟨_, _, h⟩ := rpf_bind_ok h
         obtain ⟨ord, _, h⟩ := rpf_bind_ok h
         obtain ⟨xs, _, h⟩ := rpf_bind_ok h
         obtain ⟨placed, _, h⟩ := rpf_bind_ok h
         obtain ⟨routed, hprox, h⟩ := rpf_bind_ok h
         split at h
         · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
           obtain ⟨yt, _, h⟩ := rpf_bind_ok h
           obtain ⟨resv, _, h⟩ := rpf_bind_ok h
           obtain ⟨routes, _, h⟩ := rpf_bind_ok h
           have he := Except.ok.inj h
           have hC : run.coordinateProper = placed.2.2.snd :=
             (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
           have hX : run.coordinateXs = placed.fst :=
             (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
           have hR : run.xs = routed.snd :=
             (congrArg (fun q : Graph × Run => q.2.xs) he).symm
           have hprox' : proxyWidths run.coordinateProper run.coordinateXs =
               .ok (routed.1, run.xs) := by
             rw [hC, hX, hR]; exact hprox
           obtain ⟨_, hx⟩ := (proxyWidths_rel hprox').2.2.2.2.2 i n hnode hnt
           simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
         · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
           obtain ⟨yt, _, h⟩ := rpf_bind_ok h
           obtain ⟨resv, _, h⟩ := rpf_bind_ok h
           obtain ⟨routes, _, h⟩ := rpf_bind_ok h
           have he := Except.ok.inj h
           have hC : run.coordinateProper = placed.2.2.snd :=
             (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
           have hX : run.coordinateXs = placed.fst :=
             (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
           have hR : run.xs = routed.snd :=
             (congrArg (fun q : Graph × Run => q.2.xs) he).symm
           have hprox' : proxyWidths run.coordinateProper run.coordinateXs =
               .ok (routed.1, run.xs) := by
             rw [hC, hX, hR]; exact hprox
           obtain ⟨_, hx⟩ := (proxyWidths_rel hprox').2.2.2.2.2 i n hnode hnt
           simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

 /-- Placed xs read the coordinate xs at every non-title index (region arm). -/
 private theorem rpf_place_someR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
     {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions} (rm : RegionImpl.ComponentRegions)
     (hrs : RegionImpl.newComponentRegions spec P inp cg = .ok (some rm))
     (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
     {i : Nat} {n : ProperNode}
     (hnode : run.coordinateProper.nodes[i]? = some n)
     (hnt : ¬ (n.node.border = -2 ∨ n.node.border = 2)) :
     run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
   unfold componentRunR at h
   obtain ⟨rs, hrs', h⟩ := rpf_bind_ok h
   have hrsEq : rs = some rm := Except.ok.inj (hrs'.symm.trans hrs)
   subst hrsEq
   dsimp only at h
   obtain ⟨ranked, _, h⟩ := rpf_bind_ok h
   cases ranked with
   | mk ranks rest =>
       cases rest with
       | mk cg1 rankBudget =>
         dsimp only at h
         obtain ⟨p0, _, h⟩ := rpf_bind_ok h
         obtain ⟨p, _, h⟩ := rpf_bind_ok h
         obtain ⟨_, _, h⟩ := rpf_bind_ok h
         obtain ⟨_, _, h⟩ := rpf_bind_ok h
         obtain ⟨ord, _, h⟩ := rpf_bind_ok h
         split at h
         · simp only [bind, Except.bind] at h
           exact absurd h (by simp)
         · obtain ⟨_, _, h⟩ := rpf_bind_ok h
           obtain ⟨placed, _, h⟩ := rpf_bind_ok h
           obtain ⟨routed, hprox, h⟩ := rpf_bind_ok h
           split at h
           · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
             obtain ⟨yt, _, h⟩ := rpf_bind_ok h
             obtain ⟨resv, _, h⟩ := rpf_bind_ok h
             obtain ⟨routes, _, h⟩ := rpf_bind_ok h
             have he := Except.ok.inj h
             have hC : run.coordinateProper = placed.2.2.snd :=
               (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
             have hX : run.coordinateXs = placed.fst :=
               (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
             have hR : run.xs = routed.snd :=
               (congrArg (fun q : Graph × Run => q.2.xs) he).symm
             have hprox' : proxyWidths run.coordinateProper run.coordinateXs =
                 .ok (routed.1, run.xs) := by
               rw [hC, hX, hR]; exact hprox
             obtain ⟨_, hx⟩ := (proxyWidths_rel hprox').2.2.2.2.2 i n hnode hnt
             simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
           · obtain ⟨lanes_1, _, h⟩ := rpf_bind_ok h
             obtain ⟨yt, _, h⟩ := rpf_bind_ok h
             obtain ⟨resv, _, h⟩ := rpf_bind_ok h
             obtain ⟨routes, _, h⟩ := rpf_bind_ok h
             have he := Except.ok.inj h
             have hC : run.coordinateProper = placed.2.2.snd :=
               (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
             have hX : run.coordinateXs = placed.fst :=
               (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
             have hR : run.xs = routed.snd :=
               (congrArg (fun q : Graph × Run => q.2.xs) he).symm
             have hprox' : proxyWidths run.coordinateProper run.coordinateXs =
                 .ok (routed.1, run.xs) := by
               rw [hC, hX, hR]; exact hprox
             obtain ⟨_, hx⟩ := (proxyWidths_rel hprox').2.2.2.2.2 i n hnode hnt
             simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

 /-- Title-border nodes of a region run have width zero. -/
 theorem componentRunR_title_zeroingR : componentRunR_title_zeroing_factR := by
   unfold componentRunR_title_zeroing_factR
   intro P exact spec inp cg cg' run labels orderOptions n h hmem hb
   have hCopy := h
   obtain ⟨rs, hrs', _⟩ := rpf_bind_ok hCopy
   cases rs with
   | none => exact rpf_title_noneR hrs' h hmem hb
   | some rm => exact rpf_title_someR rm hrs' h hmem hb

 /-- Placed xs read the coordinate xs at every non-title index. This is the
 strictly narrower residual of `componentRunR_placement_xs_factR` that holds
 on executed runs: the full all-index statement is false (the none-spec probe
 in `wip/Probe/RegionRunPlacementFactsTProbe.lean` exhibits title indices
 with recentered xs), while the exact twins (`X_border_record`,
 `X_nonproxy_record`) prove exactly this non-title form. -/
 theorem componentRunR_placement_xsR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
     {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions} {i : Nat} {n : ProperNode}
     (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
     (hnode : run.coordinateProper.nodes[i]? = some n)
     (hnt : ¬ (n.node.border = -2 ∨ n.node.border = 2)) :
     run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
   have hCopy := h
   obtain ⟨rs, hrs', _⟩ := rpf_bind_ok hCopy
   cases rs with
   | none => exact rpf_place_noneR hrs' h hnode hnt
   | some rm => exact rpf_place_someR rm hrs' h hnode hnt

end PipelineImpl
end Layered
end Elegant
