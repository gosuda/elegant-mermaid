import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.Pack
import Elegant.Layered.LabelsC7

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Pack

/-! ## Transport helpers

`sceneOf` transports every part-local object through its shelf origin as
`shiftRect margin margin (orientRect d canvasH (shiftRect shelfX shelfY _))`
(rects, labels, titles) and the analogous point transport for route points.
These lemmas record that this transport preserves closed containment of rects,
closed point-in-rect membership, and interior disjointness. -/

/-- Closed point-in-rect membership for a transported route point. -/
def pointInRect (R : Rect) (p : Point) : Prop :=
  R.x ≤ p.x ∧ p.x ≤ R.x + R.w ∧ R.y ≤ p.y ∧ p.y ≤ R.y + R.h

/-- Transport preserves closed containment of rectangles. -/
theorem orient_transport_contained {d : Direction} {H m : Int} {outer inner : Rect}
    (hc : outer.Contained inner) :
    (shiftRect m m (orientRect d H outer)).Contained
      (shiftRect m m (orientRect d H inner)) := by
  cases d <;>
    simp only [orientRect, shiftRect, Rect.Contained] at hc ⊢ <;> omega

/-- Transport preserves closed point-in-rect membership. -/
theorem orient_transport_point {d : Direction} {H m : Int} {p : Point} {R : Rect}
    (hp : pointInRect R p) :
    pointInRect (shiftRect m m (orientRect d H R))
      (shiftPoint m m (orientPoint d H p)) := by
  cases d <;>
    simp only [orientPoint, orientRect, shiftPoint, shiftRect, pointInRect] at hp ⊢
  <;> omega

/-- Transport preserves interior disjointness. -/
theorem orient_transport_disjoint {d : Direction} {H m : Int} {a b : Rect}
    (hd : Disjoint a b) :
    Disjoint (shiftRect m m (orientRect d H a))
      (shiftRect m m (orientRect d H b)) := by
  cases d <;>
    simp only [orientRect, shiftRect, Disjoint, Rect.meetsInterior] at hd ⊢
  <;> omega

/-- Interior meets is monotone in a larger outer rectangle on the left. -/
theorem meetsInterior_of_contained_outer {S R B : Rect}
    (hsub : S.Contained R) (h : R.meetsInterior B) : S.meetsInterior B := by
  simp only [Rect.Contained, Rect.meetsInterior] at hsub h ⊢
  obtain ⟨hx, hx2, hy, hy2⟩ := hsub
  exact ⟨by omega, by omega⟩

/-- Interior meets is monotone in a larger inner rectangle on the right. -/
theorem meetsInterior_of_contained_inner {S R B : Rect}
    (hsub : B.Contained R) (h : S.meetsInterior R) : S.meetsInterior B := by
  simp only [Rect.Contained, Rect.meetsInterior] at hsub h ⊢
  obtain ⟨hx, hx2, hy, hy2⟩ := hsub
  exact ⟨by omega, by omega⟩

/-- A packed shelf box keeps the declaring part's item dimensions at the same
index (public restatement of the `FlatC2` helper, needed for the containment
discharge). -/
theorem packShelfDims {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out)
    {k : Nat} (hk : k < out.boxes.length) (hik : k < items.length) :
    out.boxes[k].w = items[k].width ∧ out.boxes[k].h = items[k].height := by
  have hd := Pack.pack_dimensions h
  unfold Pack.dimensions at hd
  have h1 := congrArg (fun l => l[k]?) hd
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hik] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  exact h1

/-! ## Shelf geometry of one execution -/

/-- The transported shelf rect of the part packed at index `c`: the packed box,
oriented and pushed inside the canvas margin, exactly as `sceneOf` transports
every stored rect. -/
def shelfRectT {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State) (c : Nat) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (packed.boxes[c]?.getD default))

/-- Transport of a part-local rect through the shelf origin of part `c`:
`shiftRect margin margin (orientRect d canvasH (shiftRect shelfX shelfY r))`. -/
def partRectT {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State) (c : Nat) (r : Rect) : Rect :=
  shiftRect execution.params.canvasMargin execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH
      (shiftRect (packed.boxes[c]?.getD default).x
        (packed.boxes[c]?.getD default).y r))

/-- Transport of a part-local route point through the shelf origin of part `c`. -/
def partPointT {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State) (c : Nat) (p : Point) : Point :=
  shiftPoint execution.params.canvasMargin execution.params.canvasMargin
    (orientPoint o.direction execution.packedAcc.canvasH
      (shiftPoint (packed.boxes[c]?.getD default).x
        (packed.boxes[c]?.getD default).y p))

/-! ## `PartsSeparated` -/

/-- Containment half: for every executed part index `c`, every transported route
point, label rect, title rect, and box rect of the part lies inside the
transported shelf rect of `c`. This is the half discharged per item class from
the executed definitions (`PartBounded`, shelf dimensions, `packAcc` shifts). -/
def PartsContainment {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State) : Prop :=
  ∀ (c : Nat) (part : List Nat × Part),
    execution.componentsAcc.parts[c]? = some part → c < packed.boxes.length →
    ((∀ route ∈ part.2.routes, ∀ p ∈ route.2,
        pointInRect (shelfRectT execution packed c)
          (partPointT execution packed c p)) ∧
     (∀ l ∈ part.2.labels,
        (shelfRectT execution packed c).Contained
          (partRectT execution packed c l.2)) ∧
     (∀ t ∈ part.2.titles,
        (shelfRectT execution packed c).Contained
          (partRectT execution packed c t.2)) ∧
     (∀ r ∈ part.2.rects,
        (shelfRectT execution packed c).Contained
          (partRectT execution packed c r)))

/-- Disjointness half: transported shelf rects of distinct packed parts have
disjoint open interiors. -/
def PartsShelvesDisjoint {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State) : Prop :=
  ∀ (c c' : Nat), c < packed.boxes.length → c' < packed.boxes.length → c ≠ c' →
    Disjoint (shelfRectT execution packed c) (shelfRectT execution packed c')

/-- The packed shelves of one successful layered execution separate its parts:
each part's transported content stays inside its transported shelf (containment
half) and distinct shelves are pairwise interior-disjoint (disjointness half).
Only the containment half is a hypothesis-shaped fact; the disjointness half is
derived from `Pack.pack_components_disjoint`. -/
def PartsSeparated (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∃ (execution : SceneExecution inp o res) (packed : Pack.State),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed ∧
      PartsContainment execution packed ∧
      PartsShelvesDisjoint execution packed

/-- The disjointness half is not an extra assumption: it follows from the shelf
packing itself. -/
theorem partsShelvesDisjoint_of_pack {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed) :
    PartsShelvesDisjoint execution packed := by
  intro c c' hc hc' hne
  have hcD : packed.boxes[c]?.getD default = packed.boxes[c] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩]
  have hcD' : packed.boxes[c']?.getD default = packed.boxes[c'] := by
    simp [List.getElem?_eq_some_iff.mpr ⟨hc', rfl⟩]
  simp only [shelfRectT]
  rw [hcD, hcD']
  exact orient_transport_disjoint (Pack.pack_boxes_disjoint hpack c c' hc hc' hne)

/-- Build `PartsSeparated` from the containment half; the disjointness half is
derived from the packing. Consumers holding their own `SceneExecution` prove
`PartsContainment` for it and apply this. -/
theorem partsSeparated_intro {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    (hcont : PartsContainment execution packed) :
    PartsSeparated inp o res :=
  ⟨execution, packed, hpack, hcont, partsShelvesDisjoint_of_pack hpack⟩

/-- LabelsC7's packing-separation seam holds unconditionally: for the executed
packing, every transported label rect and frame rect of an executed part stays
inside that part's transported shelf rect. Discharged from `PartBounded` (the
part-local bounds) and the shelf's item dimensions (`packShelfDims`); the
transport itself only preserves the packed-local containment. -/
theorem partsSeparated_holds {inp : Input} {o : Options} {res : FamilyResult} :
    Elegant.Layered.PartsSeparated inp o res := by
  intro execution packed c part shelf hpack hmem hshelf
  obtain ⟨hbLen, hbEq⟩ := List.getElem?_eq_some_iff.mp hshelf
  have hmemlist : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hmem
  have hbounded := SceneExecution.components_parts_bounded execution part hmemlist
  unfold PartBounded at hbounded
  have hmapLen : c < (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hmem).1
  have hpartget := (List.getElem?_eq_some_iff.mp hmem).2
  have hitem : (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area))[c] =
      Pack.Item.mk part.2.width part.2.height part.2.area := by
    rw [List.getElem_map, hpartget]
  obtain ⟨hsw, hsh⟩ := packShelfDims hpack hbLen hmapLen
  subst hbEq
  have hwb : packed.boxes[c].w = part.2.width := by
    rw [hsw, hitem]
  have hhb : packed.boxes[c].h = part.2.height := by
    rw [hsh, hitem]
  refine ⟨fun l hl => ?_, fun r hr => ?_⟩
  · refine orient_transport_contained ?_
    simp only [shiftRect, Rect.Contained]
    rw [hwb, hhb]
    obtain ⟨_, _, _, _, _, hlabels⟩ := hbounded
    obtain ⟨hl1, hl2, hl3, hl4, _, _⟩ := hlabels l hl
    omega
  · refine orient_transport_contained ?_
    simp only [shiftRect, Rect.Contained]
    rw [hwb, hhb]
    obtain ⟨_, _, hrects, _, _, _⟩ := hbounded
    obtain ⟨hr1, hr2, hr3, hr4, _, _⟩ := hrects r hr
    omega

/-! ## Containment discharge from the executed definitions -/

/-- Shared executed-part data: `PartBounded` for the part and the shelf's item
dimensions (`packShelfDims`), plus the shelf-box `getD` rewrite. -/
private theorem shelfDimsOf
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    (∀ route ∈ part.2.routes, ∀ p ∈ route.2,
        0 ≤ p.x ∧ p.x ≤ part.2.width ∧ 0 ≤ p.y ∧ p.y ≤ part.2.height) ∧
      (∀ l ∈ part.2.labels,
        0 ≤ l.2.x ∧ l.2.x + l.2.w ≤ part.2.width ∧
          0 ≤ l.2.y ∧ l.2.y + l.2.h ≤ part.2.height ∧ 0 ≤ l.2.w ∧ 0 ≤ l.2.h) ∧
      (∀ t ∈ part.2.titles,
        0 ≤ t.2.x ∧ t.2.x + t.2.w ≤ part.2.width ∧
          0 ≤ t.2.y ∧ t.2.y + t.2.h ≤ part.2.height ∧ 0 ≤ t.2.w ∧ 0 ≤ t.2.h) ∧
      (∀ r ∈ part.2.rects,
        0 ≤ r.x ∧ r.x + r.w ≤ part.2.width ∧
          0 ≤ r.y ∧ r.y + r.h ≤ part.2.height ∧ 0 ≤ r.w ∧ 0 ≤ r.h) ∧
      packed.boxes[c]?.getD default = packed.boxes[c] ∧
      packed.boxes[c].w = part.2.width ∧
      packed.boxes[c].h = part.2.height := by
  have hmemlist : part ∈ execution.componentsAcc.parts := List.mem_of_getElem? hmem
  have hbounded := SceneExecution.components_parts_bounded execution part hmemlist
  unfold PartBounded at hbounded
  have hmapLen : c < (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hmem).1
  have hpartget := (List.getElem?_eq_some_iff.mp hmem).2
  have hitem : (execution.componentsAcc.parts.map
      (fun q => Pack.Item.mk q.2.width q.2.height q.2.area))[c] =
      Pack.Item.mk part.2.width part.2.height part.2.area := by
    rw [List.getElem_map, hpartget]
  obtain ⟨hsw, hsh⟩ := packShelfDims hpack hc hmapLen
  obtain ⟨_, _, hrects, htitles, hroutes, hlabels⟩ := hbounded
  refine ⟨hroutes, hlabels, htitles, hrects,
    by simp [List.getElem?_eq_some_iff.mpr ⟨hc, rfl⟩], ?_, ?_⟩
  · rw [hsw, hitem]
  · rw [hsh, hitem]

/-- The LabelsC7 packing-separation seam is exactly `PartsSeparated` for the
executed definitions: the packing itself supplies both halves. -/
theorem labelsC7_partsSeparated {inp : Input} {o : Options} {res : FamilyResult} :
    Elegant.Layered.PartsSeparated inp o res := partsSeparated_holds

/-- (a) Route points: every transported route point of an executed part lies
inside that part's transported shelf rect. -/
theorem part_route_points_within_shelf
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    ∀ route ∈ part.2.routes, ∀ p ∈ route.2,
      pointInRect (shelfRectT execution packed c)
        (partPointT execution packed c p) := by
  obtain ⟨hroutes, -, -, -, hcD, hwb, hhb⟩ := shelfDimsOf hpack hmem hc
  intro route hroute p hp
  have hpx := hroutes route hroute p hp
  simp only [shelfRectT, partPointT, hcD]
  refine orient_transport_point ?_
  simp only [pointInRect, shiftPoint]
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hpx
  rw [hwb, hhb]
  omega

/-- (b) Route labels: every transported label rect of an executed part is
contained in that part's transported shelf rect. -/
theorem part_labels_within_shelf
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    ∀ l ∈ part.2.labels,
      (shelfRectT execution packed c).Contained
        (partRectT execution packed c l.2) := by
  obtain ⟨-, hlabels, -, -, hcD, hwb, hhb⟩ := shelfDimsOf hpack hmem hc
  intro l hl
  have hlb := hlabels l hl
  simp only [shelfRectT, partRectT, hcD]
  refine orient_transport_contained ?_
  simp only [shiftRect, Rect.Contained]
  obtain ⟨hl1, hl2, hl3, hl4, -, -⟩ := hlb
  rw [hwb, hhb]
  omega

/-- (b) Titles and `ownedTextRect` fallback captions: every transported title
rect of an executed part is contained in that part's transported shelf rect. -/
theorem part_titles_within_shelf
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    ∀ t ∈ part.2.titles,
      (shelfRectT execution packed c).Contained
        (partRectT execution packed c t.2) := by
  obtain ⟨-, -, htitles, -, hcD, hwb, hhb⟩ := shelfDimsOf hpack hmem hc
  intro t ht
  have htb := htitles t ht
  simp only [shelfRectT, partRectT, hcD]
  refine orient_transport_contained ?_
  simp only [shiftRect, Rect.Contained]
  obtain ⟨ht1, ht2, ht3, ht4, -, -⟩ := htb
  rw [hwb, hhb]
  omega

/-- (c) Box and frame rects: every transported rect of an executed part is
contained in that part's transported shelf rect. -/
theorem part_rects_within_shelf
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed)
    {c : Nat} {part : List Nat × Part}
    (hmem : execution.componentsAcc.parts[c]? = some part)
    (hc : c < packed.boxes.length) :
    ∀ r ∈ part.2.rects,
      (shelfRectT execution packed c).Contained
        (partRectT execution packed c r) := by
  obtain ⟨-, -, -, hrects, hcD, hwb, hhb⟩ := shelfDimsOf hpack hmem hc
  intro r hr
  have hrb := hrects r hr
  simp only [shelfRectT, partRectT, hcD]
  refine orient_transport_contained ?_
  simp only [shiftRect, Rect.Contained]
  obtain ⟨hr1, hr2, hr3, hr4, -, -⟩ := hrb
  rw [hwb, hhb]
  omega

/-- The containment conjunct of `PartsSeparated` holds unconditionally for the
executed definitions: `PartBounded` bounds every item class in part-local
coordinates and `packShelfDims` ties the shelf to the part dimensions. -/
theorem partsContainment_of_execution
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed) :
    PartsContainment execution packed := by
  intro c part hmem hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact part_route_points_within_shelf hpack hmem hc
  · exact part_labels_within_shelf hpack hmem hc
  · exact part_titles_within_shelf hpack hmem hc
  · exact part_rects_within_shelf hpack hmem hc

/-- `PartsSeparated` for any executed `SceneExecution` with its executed
packing: the containment half from `partsContainment_of_execution`, the
disjointness half from the packing. -/
theorem partsSeparated_of_execution
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun q =>
          Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed) :
    PartsSeparated inp o res :=
  partsSeparated_intro hpack (partsContainment_of_execution hpack)

/-! ## Consumer lemmas -/

/-- A rect transported with part `c`'s shelf never meets the interior of a rect
transported with another part's shelf. -/
theorem rect_misses_box_of_distinct_parts
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hdisj : PartsShelvesDisjoint execution packed)
    {c c' : Nat} (hc : c < packed.boxes.length) (hc' : c' < packed.boxes.length)
    (hne : c ≠ c')
    {R B : Rect}
    (hR : (shelfRectT execution packed c).Contained R)
    (hB : (shelfRectT execution packed c').Contained B) :
    ¬ R.meetsInterior B := by
  intro hmeet
  exact hdisj c c' hc hc' hne
    (meetsInterior_of_contained_inner hB
      (meetsInterior_of_contained_outer hR hmeet))

/-- A transported route point of part `c` never lies strictly inside a box rect
of part `c' ≠ c`. Needs the shelf of part `c` to have positive extent (a
degenerate shelf would put the closed boundary next to the other part). -/
theorem route_misses_box_of_distinct_parts
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hdisj : PartsShelvesDisjoint execution packed)
    {c c' : Nat} (hc : c < packed.boxes.length) (hc' : c' < packed.boxes.length)
    (hne : c ≠ c')
    (hpos : 0 < (shelfRectT execution packed c).w ∧
            0 < (shelfRectT execution packed c).h)
    {q : Point} (hq : pointInRect (shelfRectT execution packed c) q)
    {B : Rect} (hB : (shelfRectT execution packed c').Contained B) :
    ¬ (B.x < q.x ∧ q.x < B.x + B.w ∧ B.y < q.y ∧ q.y < B.y + B.h) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hmeet : (shelfRectT execution packed c).meetsInterior
      (shelfRectT execution packed c') := by
    simp only [Rect.meetsInterior]
    refine ⟨?_, ?_⟩
    · have hq1 := hq.1
      have hq2 := hq.2.1
      have hb1 := hB.1
      have hb2 := hB.2.1
      have hp1 := hpos.1
      omega
    · have hq3 := hq.2.2.1
      have hq4 := hq.2.2.2
      have hb3 := hB.2.2.1
      have hb4 := hB.2.2.2
      have hp2 := hpos.2
      omega
  exact hdisj c c' hc hc' hne hmeet

/-- A transported label rect of part `c` never meets the interior of a box rect
of part `c' ≠ c`. -/
theorem label_misses_box_of_distinct_parts
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hdisj : PartsShelvesDisjoint execution packed)
    {c c' : Nat} (hc : c < packed.boxes.length) (hc' : c' < packed.boxes.length)
    (hne : c ≠ c')
    {L B : Rect}
    (hL : (shelfRectT execution packed c).Contained L)
    (hB : (shelfRectT execution packed c').Contained B) :
    ¬ L.meetsInterior B :=
  rect_misses_box_of_distinct_parts hdisj hc hc' hne hL hB

/-- Box rects transported with distinct parts' shelves have disjoint open
interiors. -/
theorem box_disjoint_of_distinct_parts
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {packed : Pack.State}
    (hdisj : PartsShelvesDisjoint execution packed)
    {c c' : Nat} (hc : c < packed.boxes.length) (hc' : c' < packed.boxes.length)
    (hne : c ≠ c')
    {B B' : Rect}
    (hB : (shelfRectT execution packed c).Contained B)
    (hB' : (shelfRectT execution packed c').Contained B') :
    Disjoint B B' := by
  intro hmeet
  exact hdisj c c' hc hc' hne
    (meetsInterior_of_contained_inner hB'
      (meetsInterior_of_contained_outer hB hmeet))

end PipelineImpl
end Elegant.Layered
