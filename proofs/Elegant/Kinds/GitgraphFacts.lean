import Elegant.Kinds.Gitgraph
import Elegant.LanesFacts

set_option autoImplicit false

/-! Facts about the gitgraph adapter: a decoded model keeps the box, route and label counts, every
commit names the branch box that is its parent, and every route joins two commits. -/

namespace Elegant
namespace Kinds
namespace Gitgraph

open Common

theorem mapM_index_record {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      xs.length = ys.length ∧
      ∀ (i : Nat) (y : β), ys[i]? = some y →
        ∃ x, xs[i]? = some x ∧ f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    change Except.ok [] = Except.ok ys at h
    injection h with heq
    subst ys
    refine ⟨rfl, ?_⟩
    intro i y hy
    simp at hy
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hf : f x with
    | error e =>
      rw [hf] at h
      change Except.error e = Except.ok ys at h
      cases h
    | ok y =>
      cases ht : xs.mapM f with
      | error e =>
        rw [hf, ht] at h
        change Except.error e = Except.ok ys at h
        cases h
      | ok tail =>
        rw [hf, ht] at h
        change Except.ok (y :: tail) = Except.ok ys at h
        injection h with heq
        subst ys
        obtain ⟨hlen, hget⟩ := ih tail ht
        refine ⟨by simp [hlen], ?_⟩
        intro i z hz
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
          subst z
          exact ⟨x, rfl, hf⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hz
          obtain ⟨a, ha, he⟩ := hget i z hz
          exact ⟨a, by simpa using ha, he⟩

theorem groups_not_exclusive {m : Model} (h : WellFormed m) {b : ModelBox} (hb : b ∈ m.boxes)
    (hr : b.role = .group) : b.exclusive = false := by
  unfold WellFormed modelWellFormed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hg⟩ := h
  have := List.all_eq_true.mp hg b hb
  simpa [hr] using this

theorem decode_facts {m : Model} {d : Decoded} (h : decode m = .ok d) :
    groupsRooted m = true ∧
    d.graph.branches.length = (m.boxes.filter (·.role == .group)).length ∧
    d.graph.commits.length = (m.boxes.filter (·.role == .node)).length ∧
    d.graph.links.length = m.routes.length ∧
    (∀ (i : Nat) (b : ModelBox), (m.boxes.filter (·.role == .node))[i]? = some b →
      ∃ cm, d.graph.commits[i]? = some cm ∧ laneIndex m b.parent = some cm.branch) ∧
    (∀ (k : Nat) (r : ModelRoute), m.routes[k]? = some r →
      ∃ l, d.graph.links[k]? = some l ∧ commitIndex m r.fromId = some l.src ∧
        commitIndex m r.toId = some l.dst) := by
  unfold decode at h
  by_cases hr : groupsRooted m = true
  · have hn : (!groupsRooted m) = false := by simp [hr]
    simp only [hn, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i caps hcaps
      split at h
      · cases h
      · rename_i slots hslots
        split at h
        · cases h
        · rename_i cms hcms
          split at h
          · cases h
          · rename_i lks hlks
            injection h with hd
            subst hd
            obtain ⟨hlc, hgc⟩ := mapM_index_record _ _ _ hcms
            obtain ⟨hll, hgl⟩ := mapM_index_record _ _ _ hlks
            have hc : cms.length = (m.boxes.filter (·.role == .node)).length := by
              simpa using hlc.symm
            refine ⟨hr, by simp, hc, by simpa using hll.symm, ?_, ?_⟩
            · intro i b hb
              have hi : i < cms.length := by
                rw [hc]
                exact (List.getElem?_eq_some_iff.mp hb).1
              have hcm : cms[i]? = some cms[i] := List.getElem?_eq_getElem hi
              obtain ⟨x, hx, hfx⟩ := hgc i _ hcm
              have hxe : x = (b, i) := by
                have := hx
                simp [List.getElem?_zipIdx, hb] at this
                exact this.symm
              subst hxe
              refine ⟨cms[i], hcm, ?_⟩
              cases hli : laneIndex m b.parent with
              | none => simp [hli] at hfx
              | some lane =>
                simp only [hli] at hfx
                have := Except.ok.inj hfx
                rw [← this]
            · intro k r hr'
              have hk : k < lks.length := by
                rw [← hll]
                exact (List.getElem?_eq_some_iff.mp hr').1
              have hlk : lks[k]? = some lks[k] := List.getElem?_eq_getElem hk
              obtain ⟨x, hx, hfx⟩ := hgl k _ hlk
              have hxe : x = r := by
                rw [hr'] at hx
                exact (Option.some.inj hx).symm
              subst hxe
              refine ⟨lks[k], hlk, ?_⟩
              cases hs : commitIndex m x.fromId with
              | none => simp [hs] at hfx
              | some src =>
                cases ht : commitIndex m x.toId with
                | none => simp [hs, ht] at hfx
                | some dst =>
                  simp only [hs, ht] at hfx
                  have := Except.ok.inj hfx
                  rw [← this]
                  exact ⟨rfl, rfl⟩
  · have hn : (!groupsRooted m) = true := by simp at hr; simp [hr]
    simp only [hn, ↓reduceIte] at h
    cases h

theorem laneIndex_spec {m : Model} {id : String} {k : Nat} (h : laneIndex m id = some k) :
    k < (m.boxes.filter (·.role == .group)).length ∧
      ∃ gb ∈ m.boxes, gb.role = .group ∧ gb.id = id := by
  unfold laneIndex at h
  obtain ⟨hk, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  have hmem := List.mem_filter.mp (List.getElem_mem hk)
  exact ⟨hk, _, hmem.1, by simpa using hmem.2, by simpa using hp⟩

theorem commitIndex_spec {m : Model} {id : String} {i : Nat} (h : commitIndex m id = some i) :
    i < (m.boxes.filter (·.role == .node)).length ∧
      ∃ nb, (m.boxes.filter (·.role == .node))[i]? = some nb ∧ nb ∈ m.boxes ∧
        nb.role = .node ∧ nb.id = id := by
  unfold commitIndex at h
  obtain ⟨hk, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  have hmem := List.mem_filter.mp (List.getElem_mem hk)
  exact ⟨hk, _, List.getElem?_eq_getElem hk, hmem.1, by simpa using hmem.2, by simpa using hp⟩

theorem laneIndex_of_group {m : Model} {gb : ModelBox} (hm : gb ∈ m.boxes)
    (hr : gb.role = .group) : ∃ k, laneIndex m gb.id = some k := by
  unfold laneIndex
  exact ⟨_, List.findIdx?_eq_some_of_exists ⟨gb, List.mem_filter.mpr ⟨hm, by simp [hr]⟩, by simp⟩⟩

theorem commitIndex_of_node {m : Model} {nb : ModelBox} (hm : nb ∈ m.boxes)
    (hr : nb.role = .node) : ∃ i, commitIndex m nb.id = some i := by
  unfold commitIndex
  exact ⟨_, List.findIdx?_eq_some_of_exists ⟨nb, List.mem_filter.mpr ⟨hm, by simp [hr]⟩, by simp⟩⟩

theorem find_id_of_nodup : ∀ (l : List ModelBox) (b : ModelBox), (l.map (·.id)).Nodup → b ∈ l →
    l.find? (fun x => x.id == b.id) = some b
  | [], b, _, h => by simp at h
  | x :: xs, b, hn, hb => by
    by_cases hx : (x.id == b.id) = true
    · have hxb : x = b := by
        rcases List.mem_cons.mp hb with h | h
        · exact h.symm
        · exfalso
          have hxi : x.id = b.id := by simpa using hx
          have := (List.nodup_cons.mp hn).1
          exact this (List.mem_map.mpr ⟨b, h, hxi.symm⟩)
      subst hxb
      simp
    · have hb' : b ∈ xs := by
        rcases List.mem_cons.mp hb with h | h
        · exfalso
          subst h
          simp at hx
        · exact h
      have hx' : (x.id == b.id) = false := by simpa using hx
      simp only [List.find?_cons, hx']
      exact find_id_of_nodup xs b (List.nodup_cons.mp hn).2 hb'

theorem eq_of_same_id {m : Model} (hu : (m.boxes.map (·.id)).Nodup) {a b : ModelBox}
    (ha : a ∈ m.boxes) (hb : b ∈ m.boxes) (hid : a.id = b.id) : a = b := by
  have h1 := find_id_of_nodup m.boxes a hu ha
  have h2 := find_id_of_nodup m.boxes b hu hb
  rw [hid] at h1
  rw [h1] at h2
  exact Option.some.inj h2

theorem dump_box? {m : Model} {d : Decoded} {res : Lanes.GitResult}
    (hu : (m.boxes.map (·.id)).Nodup) {b : ModelBox} (hb : b ∈ m.boxes) :
    (sceneOf m d res).layoutDump.box? b.id = some (dumpBox m res b) := by
  show ((dumpBoxes m res).find? fun x => x.id == b.id) = some (dumpBox m res b)
  unfold dumpBoxes
  rw [List.find?_map]
  have hc : m.boxes.find? ((fun x : Box => x.id == b.id) ∘ dumpBox m res) =
      m.boxes.find? (fun x => x.id == b.id) := rfl
  rw [hc, find_id_of_nodup m.boxes b hu hb]
  rfl

theorem decoded_wf {m : Model} {d : Decoded} (hd : decode m = .ok d) : d.graph.WF := by
  obtain ⟨_, hbr, hco, hlk, hcom, hlnk⟩ := decode_facts hd
  refine ⟨?_, ?_⟩
  · intro cm hcm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcm
    have hi' : i < (m.boxes.filter (·.role == .node)).length := by
      rw [← hco]
      exact (List.getElem?_eq_some_iff.mp hi).1
    have hnb : (m.boxes.filter (·.role == .node))[i]? = some (m.boxes.filter (·.role == .node))[i] :=
      List.getElem?_eq_getElem hi'
    obtain ⟨cm', hcm', hlane⟩ := hcom i _ hnb
    rw [hi] at hcm'
    have hce := Option.some.inj hcm'
    subst hce
    rw [hbr]
    exact (laneIndex_spec hlane).1
  · intro l hl
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl
    have hk' : k < m.routes.length := by
      rw [← hlk]
      exact (List.getElem?_eq_some_iff.mp hk).1
    have hrk : m.routes[k]? = some m.routes[k] := List.getElem?_eq_getElem hk'
    obtain ⟨l', hl', hs, ht⟩ := hlnk k _ hrk
    rw [hk] at hl'
    have hle := Option.some.inj hl'
    subst hle
    rw [hco]
    exact ⟨(commitIndex_spec hs).1, (commitIndex_spec ht).1⟩

theorem group_rect {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hd : decode m = .ok d) (hc : c.Pos) (hres : res = Lanes.frameOf d.graph c m.profile)
    {b : ModelBox} (hb : b ∈ m.boxes) (hr : b.role = .group) :
    ∃ k, laneIndex m b.id = some k ∧ k < d.graph.branches.length ∧
      boxRect m res b =
        Lanes.shiftRect (Lanes.frameDx d.graph c m.profile) (Lanes.frameDy d.graph c m.profile)
          (Lanes.laneBandOf d.graph c k) := by
  obtain ⟨k, hk⟩ := laneIndex_of_group hb hr
  have hkb : k < d.graph.branches.length := by
    obtain ⟨_, hbr, _⟩ := decode_facts hd
    rw [hbr]
    exact (laneIndex_spec hk).1
  refine ⟨k, hk, hkb, ?_⟩
  have hfl := (Lanes.frame_lane d.graph c m.profile hc hkb).1
  subst hres
  simp only [boxRect, hr, hk, Option.bind_some, hfl, Option.getD_some]

theorem node_rect {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hwf : WellFormed m) (hd : decode m = .ok d) (hc : c.Pos)
    (hres : res = Lanes.frameOf d.graph c m.profile)
    {b : ModelBox} (hb : b ∈ m.boxes) (hr : b.role = .node) :
    ∃ i cm P, commitIndex m b.id = some i ∧ i < d.graph.commits.length ∧
      d.graph.commits[i]? = some cm ∧ laneIndex m b.parent = some cm.branch ∧
      res.points[i]? = some P ∧
      P = Lanes.shiftPoint (Lanes.frameDx d.graph c m.profile) (Lanes.frameDy d.graph c m.profile)
        ((Lanes.Shape.of d.graph c).commitPoint d.graph i) ∧
      boxRect m res b = ⟨P.x, P.y, 0, 0⟩ := by
  obtain ⟨i, hi⟩ := commitIndex_of_node hb hr
  obtain ⟨hilt, nb, hnb, hnbm, _, hnbid⟩ := commitIndex_spec hi
  have hnbb : nb = b := eq_of_same_id (Model.boxIds_nodup hwf) hnbm hb hnbid
  subst hnbb
  obtain ⟨_, _, hco, _, hcom, _⟩ := decode_facts hd
  obtain ⟨cm, hcm, hlane⟩ := hcom i _ hnb
  have hic : i < d.graph.commits.length := by
    rw [hco]
    exact hilt
  have hfp := (Lanes.frame_point d.graph c m.profile hc (decoded_wf hd) hic).1
  subst hres
  refine ⟨i, cm, _, hi, hic, hcm, hlane, hfp, rfl, ?_⟩
  simp only [boxRect, hr, hi, Option.bind_some, hfp]

theorem node_flat {m : Model} {res : Lanes.GitResult} {b : ModelBox} (hr : b.role = .node) :
    (boxRect m res b).w = 0 ∧ (boxRect m res b).h = 0 := by
  simp only [boxRect, hr]
  split <;> simp [Lanes.zeroRect]

theorem group_flat {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hd : decode m = .ok d) (hc : c.Pos) (hres : res = Lanes.frameOf d.graph c m.profile)
    {b : ModelBox} (hb : b ∈ m.boxes) (hr : b.role = .group) :
    (boxRect m res b).w = 0 ∨ (boxRect m res b).h = 0 := by
  obtain ⟨k, _, hkb, hrect⟩ := group_rect hd hc hres hb hr
  have hfl := Lanes.frame_lane d.graph c m.profile hc hkb
  rw [hrect]
  simpa [Lanes.shiftRect] using hfl.2.2.2.2.2

theorem exclusive_node {m : Model} (hwf : WellFormed m) {b : ModelBox} (hb : b ∈ m.boxes)
    (hex : b.exclusive = true) : b.role = .node := by
  cases hr : b.role with
  | node => rfl
  | group =>
    have := groups_not_exclusive hwf hb hr
    rw [hex] at this
    cases this

theorem mem_dump_boxes {m : Model} {d : Decoded} {res : Lanes.GitResult} {b' : Box}
    (hb' : b' ∈ (sceneOf m d res).layoutDump.boxes) : ∃ b ∈ m.boxes, dumpBox m res b = b' := by
  have hb'' : b' ∈ m.boxes.map (dumpBox m res) := hb'
  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hb''
  exact ⟨b, hb, hbe⟩

theorem mem_dump_routes {m : Model} {d : Decoded} {res : Lanes.GitResult} {r' : Route}
    (hr' : r' ∈ (sceneOf m d res).layoutDump.routes) :
    ∃ (r : ModelRoute) (i : Nat), m.routes[i]? = some r ∧
      r' = ⟨r.id, r.fromId, r.toId, r.orthogonal, res.routes.getD i []⟩ := by
  have hr'' : r' ∈ m.routes.zipIdx.map
      (fun (x : ModelRoute × Nat) => (⟨x.1.id, x.1.fromId, x.1.toId, x.1.orthogonal,
        res.routes.getD x.2 []⟩ : Route)) := hr'
  obtain ⟨⟨r, i⟩, hmem, hre⟩ := List.mem_map.mp hr''
  exact ⟨r, i, List.mem_zipIdx_iff_getElem?.mp hmem, hre.symm⟩

theorem disjoint_of_flat {a b : Rect} (h : a.w = 0 ∨ a.h = 0) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem disjoint_of_flat' {a b : Rect} (h : b.w = 0 ∨ b.h = 0) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem onBoundary_point (p : Point) : Validator.onBoundary p ⟨p.x, p.y, 0, 0⟩ := by
  simp only [Validator.onBoundary]
  omega

/-- An end of a route: the dump box of the commit and the point of the commit. -/
theorem endpoint {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hwf : WellFormed m) (hd : decode m = .ok d) (hc : c.Pos)
    (hres : res = Lanes.frameOf d.graph c m.profile) {id : String} {j : Nat}
    (hj : commitIndex m id = some j) :
    ∃ P nb, (sceneOf m d res).layoutDump.box? id = some (dumpBox m res nb) ∧
      res.points[j]? = some P ∧ Validator.onBoundary P (dumpBox m res nb).rect := by
  obtain ⟨_, nb, _, hnbm, hnbr, hnbid⟩ := commitIndex_spec hj
  obtain ⟨i', _, P, hi', _, _, _, hPt, _, hrect⟩ := node_rect hwf hd hc hres hnbm hnbr
  rw [hnbid, hj] at hi'
  have hij := Option.some.inj hi'
  subst hij
  refine ⟨P, nb, ?_, hPt, ?_⟩
  · rw [← hnbid]
    exact dump_box? (Model.boxIds_nodup hwf) hnbm
  · show Validator.onBoundary P (boxRect m res nb)
    rw [hrect]
    exact onBoundary_point P

theorem clause1 {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hwf : WellFormed m) (hd : decode m = .ok d) (hc : c.Pos)
    (hres : res = Lanes.frameOf d.graph c m.profile) :
    Validator.C1 (sceneOf m d res).layoutDump := by
  intro b' hb'
  obtain ⟨b, hb, rfl⟩ := mem_dump_boxes hb'
  show Rect.Contained (Validator.canvasRect _) (boxRect m res b)
  cases hr : b.role with
  | group =>
    obtain ⟨k, _, hkb, hrect⟩ := group_rect hd hc hres hb hr
    obtain ⟨_, h1, h2, h3, h4, _⟩ := Lanes.frame_lane d.graph c m.profile hc hkb
    rw [hrect]
    subst hres
    simp only [Validator.canvasRect, Rect.Contained, Lanes.shiftRect, sceneOf, Scene.layoutDump]
    omega
  | node =>
    obtain ⟨i, cm, P, _, hic, _, _, _, hP, hrect⟩ := node_rect hwf hd hc hres hb hr
    obtain ⟨_, _, h1, h2, h3, h4, _⟩ := Lanes.frame_point d.graph c m.profile hc (decoded_wf hd) hic
    rw [hrect]
    subst hres
    subst hP
    simp only [Validator.canvasRect, Rect.Contained, Lanes.shiftPoint, sceneOf, Scene.layoutDump]
    omega

theorem clause2 {m : Model} {d : Decoded} {res : Lanes.GitResult}
    (hwf : WellFormed m) :
    Validator.C2 (sceneOf m d res).layoutDump := by
  intro b1 hb1 _ _ _ hex1 _ _
  obtain ⟨x1, hx1, rfl⟩ := mem_dump_boxes hb1
  have hr := exclusive_node hwf hx1 hex1
  exact disjoint_of_flat (Or.inl (node_flat hr).1)

theorem clause3 {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hwf : WellFormed m) (hd : decode m = .ok d) (hc : c.Pos)
    (hres : res = Lanes.frameOf d.graph c m.profile) :
    Validator.C3 (sceneOf m d res).layoutDump := by
  intro b' hb' hne p hp
  obtain ⟨b, hb, rfl⟩ := mem_dump_boxes hb'
  have hne' : b.parent ≠ "" := hne
  have hp' : (sceneOf m d res).layoutDump.box? b.parent = some p := hp
  cases hr : b.role with
  | group =>
    obtain ⟨hroot, _⟩ := decode_facts hd
    have := List.all_eq_true.mp hroot b hb
    simp [hr] at this
    exact absurd this hne'
  | node =>
    obtain ⟨i, cm, P, _, hic, hcm, hlane, _, hP, hrect⟩ := node_rect hwf hd hc hres hb hr
    obtain ⟨_, gb, hgbm, hgbr, hgbid⟩ := laneIndex_spec hlane
    have hbox := dump_box? (d := d) (res := res) (Model.boxIds_nodup hwf) hgbm
    rw [hgbid, hp'] at hbox
    have hpe : p = dumpBox m res gb := Option.some.inj hbox
    subst hpe
    obtain ⟨k, hk, _, hrectg⟩ := group_rect hd hc hres hgbm hgbr
    have hkc : k = cm.branch := by
      rw [hgbid, hlane] at hk
      exact (Option.some.inj hk).symm
    show Rect.Contained (boxRect m res gb) (boxRect m res b)
    rw [hrectg, hrect, hkc]
    have hfp := Lanes.frame_point d.graph c m.profile hc (decoded_wf hd) hic
    have hbo : Lanes.branchOf d.graph i = cm.branch := by simp [Lanes.branchOf, hcm]
    have hcont := hfp.2.2.2.2.2.2
    rw [hbo] at hcont
    have hsh := (Lanes.shiftRect_contained (Lanes.frameDx d.graph c m.profile)
      (Lanes.frameDy d.graph c m.profile)).mpr hcont
    subst hP
    exact hsh

theorem clause4 {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hd : decode m = .ok d) (hres : res = Lanes.frameOf d.graph c m.profile) :
    Validator.C4 (sceneOf m d res).layoutDump := by
  intro r' hr' _
  obtain ⟨r, i, hri, rfl⟩ := mem_dump_routes hr'
  obtain ⟨l, hl, _, _⟩ := (decode_facts hd).2.2.2.2.2 i r hri
  obtain ⟨pts, hpts, horth, _, _⟩ := Lanes.frame_route d.graph c m.profile (decoded_wf hd) hl
  show Polyline.isOrthogonal (res.routes.getD i []) = true
  subst hres
  rw [List.getD_eq_getElem?_getD]
  have : (Lanes.frameOf d.graph c m.profile).routes[i]? = some pts := hpts
  rw [this]
  exact horth

theorem clause5 {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hwf : WellFormed m) (hd : decode m = .ok d) (hc : c.Pos)
    (hres : res = Lanes.frameOf d.graph c m.profile) :
    Validator.C5 (sceneOf m d res).layoutDump := by
  intro r' hr'
  obtain ⟨r, i, hri, rfl⟩ := mem_dump_routes hr'
  obtain ⟨l, hl, hs, ht⟩ := (decode_facts hd).2.2.2.2.2 i r hri
  obtain ⟨pts, hpts, _, hhead, hlast⟩ := Lanes.frame_route d.graph c m.profile (decoded_wf hd) hl
  obtain ⟨P, nb, hbs, hPs, hon⟩ := endpoint hwf hd hc hres hs
  obtain ⟨Q, nb', hbt, hQt, hon'⟩ := endpoint hwf hd hc hres ht
  have hrp : res.routes.getD i [] = pts := by
    subst hres
    rw [List.getD_eq_getElem?_getD]
    have : (Lanes.frameOf d.graph c m.profile).routes[i]? = some pts := hpts
    rw [this]
    rfl
  refine ⟨P, Q, dumpBox m res nb, dumpBox m res nb', ?_, ?_, hbs, hbt, hon, hon'⟩
  · show (res.routes.getD i []).head? = some P
    rw [hrp, hhead]
    subst hres
    exact hPs
  · show (res.routes.getD i []).getLast? = some Q
    rw [hrp, hlast]
    subst hres
    exact hQt

theorem clause6 {m : Model} {d : Decoded} {res : Lanes.GitResult}
    (hwf : WellFormed m) :
    Validator.C6 (sceneOf m d res).layoutDump := by
  intro _ _ b' hb' hex _ h
  obtain ⟨b, hb, rfl⟩ := mem_dump_boxes hb'
  have hr := exclusive_node hwf hb hex
  have hw : (boxRect m res b).w = 0 := (node_flat hr).1
  have h0 : 0 < (boxRect m res b).w := h.1
  omega

theorem clause7 {m : Model} {d : Decoded} {res : Lanes.GitResult}
    (hwf : WellFormed m) :
    Validator.C7 (sceneOf m d res).layoutDump := by
  intro l _ b' hb' hex _
  obtain ⟨b, hb, rfl⟩ := mem_dump_boxes hb'
  have hr := exclusive_node hwf hb hex
  exact disjoint_of_flat' (Or.inl (node_flat hr).1)

theorem clause8 {m : Model} {d : Decoded} {c : Lanes.GitConsts} {res : Lanes.GitResult}
    (hd : decode m = .ok d) (hc : c.Pos) (hres : res = Lanes.frameOf d.graph c m.profile) :
    Validator.C8 (sceneOf m d res).layoutDump := by
  have hflat : ∀ g' ∈ (sceneOf m d res).layoutDump.boxes, g'.role = "group" →
      g'.rect.w = 0 ∨ g'.rect.h = 0 := by
    intro g' hg' hrole
    obtain ⟨gb, hgb, rfl⟩ := mem_dump_boxes hg'
    have hr : gb.role = .group := by
      cases hgr : gb.role with
      | group => rfl
      | node =>
        have : gb.role.id = "group" := hrole
        rw [hgr] at this
        simp [BoxRole.id] at this
    exact group_flat hd hc hres hgb hr
  refine ⟨?_, ?_⟩
  · intro g' hg' hrole b _ _ _ _
    exact disjoint_of_flat (hflat g' hg' hrole)
  · intro g' hg' hrole l _
    exact Or.inl (disjoint_of_flat (hflat g' hg' hrole))

theorem layout_decompose {m : Model} {r : Layered.FamilyResult} (hl : layout m = .ok r) :
    ∃ (d : Decoded) (res : Lanes.GitResult) (c : Lanes.GitConsts), decode m = .ok d ∧
      Lanes.GitConsts.load m.profile = .ok c ∧ res = Lanes.frameOf d.graph c m.profile ∧
      r.scene = sceneOf m d res := by
  unfold layout at hl
  cases hsc : scene m with
  | error e =>
    simp only [hsc] at hl
    cases hl
  | ok s =>
    simp only [hsc] at hl
    have hrs : r.scene = s := by
      have := Except.ok.inj hl
      rw [← this]
    unfold scene at hsc
    cases hd : decode m with
    | error e =>
      simp only [hd] at hsc
      cases hsc
    | ok d =>
      cases hg : Lanes.gitgraph d.graph m.profile with
      | error e =>
        simp [hd, hg, bind, Except.bind] at hsc
      | ok res =>
        simp only [hd, hg, bind, Except.bind, pure, Except.pure] at hsc
        have hse := Except.ok.inj hsc
        obtain ⟨_, c, hload, hres⟩ := Lanes.gitgraph_frame hg
        exact ⟨d, res, c, by first | exact hd | rfl, hload, hres, by rw [hrs, ← hse]⟩

theorem decode_direction {m : Model} {d : Decoded} (h : decode m = .ok d) :
    d.graph.direction = m.options.direction := by
  unfold decode at h
  by_cases hr : groupsRooted m = true
  · have hn : (!groupsRooted m) = false := by simp [hr]
    simp only [hn, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · injection h with hd
            subst hd
            rfl
  · have hn : (!groupsRooted m) = true := by simp at hr; simp [hr]
    simp only [hn, ↓reduceIte] at h
    cases h

/-- A model laid out from right to left is rejected, as the header `gitGraph RL:` is. -/
theorem layout_rejects_rl {m : Model} {d : Decoded} (hd : decode m = .ok d)
    (h : m.options.direction = .RL) : layout m = .error (.geometry .domain) := by
  have hrl : d.graph.direction = .RL := by rw [decode_direction hd, h]
  unfold layout scene
  simp only [hd, bind, Except.bind, Lanes.gitgraph_rejects_rl d.graph m.profile hrl]

/-- Every gitgraph layout satisfies the hard constraints of the validator. -/
theorem layout_valid {m : Model} {r : Layered.FamilyResult} (hwf : WellFormed m)
    (hl : layout m = .ok r) : HardConstraints r.scene.layoutDump := by
  obtain ⟨d, res, c, hd, hload, hres, hs⟩ := layout_decompose hl
  have hc : c.Pos := Lanes.load_pos hload
  rw [hs]
  exact ⟨clause1 hwf hd hc hres, clause2 hwf, clause3 hwf hd hc hres, clause4 hd hres,
    clause5 hwf hd hc hres, clause6 hwf, clause7 hwf, clause8 hd hc hres⟩
end Gitgraph
end Kinds
end Elegant
