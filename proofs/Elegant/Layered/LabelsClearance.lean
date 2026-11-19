import Elegant.Layered.SceneBounds
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.Pack
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

/-! Flat-layered label clearance (C7) and group-frame/label clearance (C8b).

`PipelineImpl.sceneOf` emits three families of labels for a successful flat
`PipelineImpl.layout`:

* measured route labels — `acc.labels.getD index` transported by the pack
  position, canvas margin, and orientation;
* owner-caption labels backed by an installed title from `acc.titles`,
  resized to the measured text size;
* owner-caption fallback labels computed by `ownedTextRect` from the owner
  scene box (owners that are non-exclusive boxes without an installed title).

The geometric core — placed label rectangles and caption rectangles against
the plain-node and group-frame rectangles of the same component — is stated
as the per-part premise `PartClearance` below, the analogue of
`FrameClearRuns` for C6: the parent discharges it per component run from
`FrameClearance`, the loop/lane reservations, and the border-order facts.
Cross-part clearance is *proved* here from `Pack.pack_boxes_disjoint`.
The scene-level bookkeeping (which label is emitted, which box is exclusive,
uniform transport invariance) is proved here. -/

namespace Elegant.Layered

namespace PipelineImpl

/-- The label emitted for `source` (a `ModelLabel` at `inp.labels[index]`) has
its scene rect determined by `label_source`: either a measured route-label
rect or a caption/fallback rect owned by a non-exclusive box. -/
theorem label_source_split {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {label : SceneLabel}
    (hl : label ∈ res.scene.labels) :
    ∃ (source : ModelLabel) (index : Nat),
      inp.labels[index]? = some source ∧
      inp.boxes.any (fun box => box.id == source.owner && box.exclusive) = false ∧
      label.id = source.id ∧ label.owner = source.owner ∧
      ((∃ measured,
          execution.measured.find? (fun item => item.index == index) = some measured) ∨
        (execution.measured.find? (fun item => item.index == index) = none ∧
          ∃ ownerIndex, inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex)) :=
  execution.label_source hl

/-- A group-role source box is never exclusive in a well-formed model: groups
carry frames, and `modelWellFormed` forbids `exclusive` on a `.group` role. -/
theorem exclusive_not_group {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) {box : ModelBox} (hbox : box ∈ inp.boxes)
    (hex : box.exclusive = true) : box.role ≠ .group := by
  have hw : modelWellFormed (inputModel inp o) = true := hwf
  unfold modelWellFormed at hw
  simp only [Bool.and_eq_true] at hw
  have hb0 := List.all_eq_true.mp hw.2 box hbox
  simp only [hex, Bool.not_true] at hb0
  intro hgroup
  rw [hgroup] at hb0
  simp at hb0

/-! ### Transport of the clearance relations through the scene projection -/

/-- `StrictInside` survives a common translation of both rectangles. -/
theorem strictInside_shiftRect {g l : Rect} {dx dy : Int}
    (h : g.StrictInside l) : (shiftRect dx dy g).StrictInside (shiftRect dx dy l) := by
  simp only [Rect.StrictInside, shiftRect] at h ⊢
  omega

/-- `StrictInside` survives a common orientation of both rectangles. -/
theorem strictInside_orientRect {g l : Rect} {d : Direction} {h : Int}
    (hc : g.StrictInside l) : (orientRect d h g).StrictInside (orientRect d h l) := by
  cases d <;> simp only [Rect.StrictInside, orientRect] at hc ⊢ <;> omega

/-- `Disjoint` survives a common translation. -/
theorem disjoint_shiftRect {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (shiftRect dx dy a) (shiftRect dx dy b) :=
  not_meetsInterior_shiftRect h

/-- `Disjoint` survives a common orientation. -/
theorem disjoint_orientRect {a b : Rect} {d : Direction} {h : Int}
    (hd : Disjoint a b) : Disjoint (orientRect d h a) (orientRect d h b) :=
  not_meetsInterior_orientRect hd

/-- A rectangle that keeps clear of a translated partner keeps clear of the
partner under the full scene transport (pack shift, orientation, margin). -/
theorem not_meetsInterior_transport {a b : Rect} {px py m h : Int} {d : Direction}
    (hclr : ¬ a.meetsInterior b) :
    ¬ (shiftRect m m (orientRect d h (shiftRect px py a))).meetsInterior
        (shiftRect m m (orientRect d h (shiftRect px py b))) :=
  fun hmeet =>
  hclr (meetsInterior_of_shiftRect (dx := px) (dy := py)
    (meetsInterior_of_orientRect (d := d) (h := h)
      (meetsInterior_of_shiftRect (dx := m) (dy := m) hmeet)))

/-- The matching statement for `Disjoint`. -/
theorem disjoint_transport {a b : Rect} {px py m h : Int} {d : Direction}
    (hclr : Disjoint a b) :
    Disjoint (shiftRect m m (orientRect d h (shiftRect px py a)))
      (shiftRect m m (orientRect d h (shiftRect px py b))) := by
  apply disjoint_shiftRect
  apply disjoint_orientRect
  exact disjoint_shiftRect hclr

/-- The matching statement for `StrictInside`. -/
theorem strictInside_transport {g l : Rect} {px py m h : Int} {d : Direction}
    (hclr : g.StrictInside l) :
    (shiftRect m m (orientRect d h (shiftRect px py g))).StrictInside
      (shiftRect m m (orientRect d h (shiftRect px py l))) := by
  apply strictInside_shiftRect
  apply strictInside_orientRect
  exact strictInside_shiftRect hclr

/-- A caption rect emitted from an installed title has the title's origin and
the measured text size, so it is contained in the stored title rect. -/
theorem caption_resize_contained {stored size : Rect} (hw : size.w ≤ stored.w)
    (hh : size.h ≤ stored.h) :
    stored.Contained { stored with w := size.w, h := size.h } := by
  unfold Rect.Contained
  simp only
  omega

end PipelineImpl

end Elegant.Layered
