import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

/-!
# The per-expansion step of the C6 recursion lift, reduced to named remainders

`layoutRecursive_c6_of_flat` consumes `ExpandChildC6Step` for every
`expandChild` call the recursion performs.  This module assembles that step
package from two named remainders:

* `ExpandChildC6Geometry` — the two genuinely cross-scene clearance facts:
  a shifted child route misses an exclusive parent-scene box outside the
  expanded group's scope, and a parent-scene route misses every inserted
  child box;
* `ExpandChildC6Anchors` — the scope anchors `group.id :: ancestors
  group.id` of the expanded group on the endpoints of every child-scene
  route inside the merged dump.

Everything else the step asks for — the box-lookup transports of both merged
scenes and the two scene-size bounds — is proved here from the expansion's
assembly sources (`expandChild_sources`, `expandChild_selected_ids`,
`expandChild_merge_bounds`).

Unlike the C7/C8a/C8b step predicates before their repair,
`ExpandChildC6Step` does not quantify over unconstrained title lines: its own
premises pin `titleLines` to the wrapped group title (the `metricOf` and
`StyledMeasure.wrap` equations) and then pin `dx`/`dy` to the offsets
computed from that title, which are exactly the values the executed
`expandChild` stored in the merged scene.  The step therefore needs no
`ExpandChildTitleWrapped` premise; the pinning happens inside the proof
below.
-/

namespace Elegant.Layered.PipelineImpl

/-- The genuinely geometric remainder of `ExpandChildC6Step`: the two
cross-scene clearance pairs (a shifted child route vs an exclusive
parent-scene box outside the expanded group's scope, and a parent-scene
route vs an inserted child box).  Box-lookup transport, scene sizes, and the
scope anchors are structural and live in `ExpandChildC6Anchors` or are
proved outright. -/
def ExpandChildC6Geometry (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child _result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ cr ∈ child.scene.routes, ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
        ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) pb.rect) ∧
    (∀ pr ∈ parent.scene.routes, ∀ cb ∈ child.scene.boxes, cb.exclusive = true →
        ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect))

/-- The scope-anchor remainder of `ExpandChildC6Step`: every anchor id of the
expanded group (`group.id` and its parent-scene ancestors) lies on the
ancestor chain of an endpoint of every child-scene route, inside the merged
dump.  This presupposes the scene ancestry the merged dump built (embedded
child roots point at the group), which no proved fact of the expansion or
the recursion supplies here. -/
def ExpandChildC6Anchors (group : ModelBox) (parent child result : FamilyResult) : Prop :=
  ∀ rt ∈ child.scene.routes,
    ∀ x ∈ (group.id :: parent.scene.layoutDump.ancestors group.id),
      x ∈ result.scene.layoutDump.ancestors rt.fromId ∨
        x ∈ result.scene.layoutDump.ancestors rt.toId

/-- The `hgeo` shape `layoutRecursive_c6_of_flat` consumes: every
`expandChild` call `layoutRecursive` performs satisfies `ExpandChildC6Step`,
discharged from the named geometric and anchor remainders.  The box-lookup
transports and the scene-size bounds are proved from the expansion's
assembly at the offsets the run itself used, which the step's own premises
pin. -/
theorem expandChild_c6_step_of_geometry
    (hgeoC6 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Geometry P inp o group titleHeight parent child res)
    (hanchorC6 : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Anchors group parent child res) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  have hanch := hanchorC6 fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hgeo := hgeoC6 fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, hexpand'⟩ := hctx
  intro frame metric tl _lines dx dy hframe hmetric htitle _hlines hdx hdy
  have hwrap : ExpandChildTitleWrapped P inp o group tl := ⟨metric, hmetric, htitle⟩
  -- pin the caller's frame, metric, lines, and offsets to the run's own
  obtain ⟨frame₀, metric₀, tl₀, _lines₀, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _hlines₀,
    hdx₀, hdy₀, _hcanvas, hboxes⟩ := expandChild_sources hexpand'
  have hff : frame₀ = frame := Option.some.inj (hframe₀.symm.trans hframe)
  rw [hff] at hdx₀ hdy₀
  have hmetricEq : metric = metric₀ := Except.ok.inj (hmetric.symm.trans hmetric₀)
  rw [hmetricEq] at htitle
  have htl : tl = tl₀ := Except.ok.inj (htitle.symm.trans htitle₀)
  rw [← htl] at hdx₀ hdy₀
  have hdxEq : dx = dx₀ := by omega
  have hdyEq : dy = dy₀ := by omega
  rw [← hdxEq, ← hdyEq] at hboxes
  -- the id partition of the two sub-scenes
  obtain ⟨hcid, hpid, hnC, hnP, hdisj⟩ := expandChild_selected_ids hwf hchild hparent
  have hb := expandChild_merge_bounds hwf hgroup hchild hparent hexpand'
  obtain ⟨hg1, hg2⟩ := hgeo frame tl dx dy hframe hdx hdy hwrap
  refine ⟨?_, ?_, hb.1, hb.2.1, hg1, hg2, hanch⟩
  · intro b hb
    have hbMem : b ∈ child.scene.boxes := List.mem_of_find?_eq_some hb
    have hidC : b.id ∈ (inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hcid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidC
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hchildFirst : ∀ (cb : Box), cb ∈ child.scene.boxes → cb.id = b.id → cb = b := by
      intro cb hcbmem hcbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hcid]; exact hnC) hcbmem hbMem hcbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some (embedBox group.id dx dy b)
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := embedBox group.id dx dy b) (s := b.id)
      ⟨m, hmin, ?_⟩ rfl ?_
    · have hcf : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = some (embedBox group.id dx dy b) := by
        rw [List.find?_map]
        have hinside : (child.scene.boxes.find?
            ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy)) = some b := by
          have hpred : ((fun box : Box => box.id == m.id) ∘ embedBox group.id dx dy) =
              (fun cb => cb.id == b.id) := by
            funext cb
            simp only [Function.comp_apply, embedBox]
            rw [hmid]
          rw [hpred]
          exact hb
        rw [hinside]
        rfl
      rw [List.find?_append]
      rw [hcf]
      rfl
    · intro m' _hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        rw [hchildFirst cb hcb hcbkey]
      · exfalso
        exact hdisj z.id
          (by rw [hzid, ← hcid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
          (by rw [← hpid]; exact List.mem_map.mpr ⟨z, hzp, rfl⟩)
  · intro b hb
    have hbMem : b ∈ parent.scene.boxes := List.mem_of_find?_eq_some hb
    have hidP : b.id ∈ (inp.boxes.filter
        (fun box => !Compound.inside inp.boxes group.id box.id)).map (·.id) := by
      rw [← hpid]
      exact List.mem_map.mpr ⟨b, hbMem, rfl⟩
    obtain ⟨m, hmf, hmid⟩ := List.mem_map.mp hidP
    obtain ⟨hmin, _hinside⟩ := List.mem_filter.mp hmf
    have hparentFirst : ∀ (pb : Box), pb ∈ parent.scene.boxes → pb.id = b.id → pb = b := by
      intro pb hpmem hpbid
      exact expandChild_nodup_map_inj (·.id)
        (by rw [hpid]; exact hnP) hpmem hbMem hpbid
    show res.scene.boxes.find? (fun x => x.id == b.id) = some b
    rw [hboxes]
    refine expandChild_find?_filterMap_eq_some (fun model : ModelBox =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id))
      (fun z : Box => z.id) (y := b) (s := b.id) ⟨m, hmin, ?_⟩ rfl ?_
    · have hcfNone : (child.scene.boxes.map (embedBox group.id dx dy)).find?
          (fun box => box.id == m.id) = none := by
        rw [List.find?_eq_none]
        intro cb hcb hp
        obtain ⟨cd, hcd, hcdrfl⟩ := List.mem_map.mp hcb
        subst hcdrfl
        have hkey : (embedBox group.id dx dy cd).id = m.id := beq_iff_eq.mp hp
        rw [show (embedBox group.id dx dy cd).id = cd.id from rfl] at hkey
        exact hdisj cd.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cd, hcd, rfl⟩)
          (by rw [hkey]; exact List.mem_map.mpr ⟨m, hmf, rfl⟩)
      have hcfP : parent.scene.boxes.find? (fun box => box.id == m.id) = some b := by
        show parent.scene.layoutDump.box? m.id = some b
        rw [hmid]
        exact hb
      rw [List.find?_append, hcfNone, hcfP]
      rfl
    · intro m' _hm' z hz hzid
      have hzmem : z ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hz
      rcases List.mem_append.mp hzmem with hzc | hzp
      · obtain ⟨cb, hcb, rfl⟩ := List.mem_map.mp hzc
        have hcbkey : cb.id = b.id := by
          rw [show (embedBox group.id dx dy cb).id = cb.id from rfl] at hzid
          exact hzid
        exfalso
        exact hdisj cb.id
          (by rw [← hcid]; exact List.mem_map.mpr ⟨cb, hcb, rfl⟩)
          (by rw [hcbkey, ← hpid]; exact List.mem_map.mpr ⟨b, hbMem, rfl⟩)
      · rw [hparentFirst z hzp hzid]

end Elegant.Layered.PipelineImpl
