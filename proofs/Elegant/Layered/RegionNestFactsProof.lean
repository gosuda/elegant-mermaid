import Elegant.Layered.RegionNestCoords
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open CoordsImpl
open RegionImpl

/-! # Region frame-nesting allocation core (`R_RegionNestAllocCore`).

Proves the two region residuals from one open core:
`R_regionNestSomeResidual_of_allocCore` derives the plain-member x-bracket
(`R_RegionNestSomeResidual`) and `R_regionNestGroupResidual_of_allocCore`
derives child-group containment (`R_RegionNestGroupResidual`), each from
`R_RegionNestAllocCore` plus generic frame/hull facts. The core stays open.

What is proved and what is open: both reductions are proved outright from
the core. The core itself (correspondence, nesting transitivity, side
existence, per-side horizontal inclusion, member-vs-marker ordering) is the
single remaining open def; it is the `crossCoordsR` allocation remainder.
No `spec'`/stage split is needed: the core is uniform over `none` and `some`
specs and over idle and region-active runs, so the exact hull argument
replays without case analysis once the core is assumed.

Probe evidence (`proofs/wip/Probe/RegionNestFactsTProbe.lean`,
`RegionNestFactsTCore.lean`, `RegionNestFactsTNarrow.lean`, each evaluated on
executed `componentRunR` runs over all components and candidates `0-4`):

| input | plain bracket | group containment | core (corr/side/nest/horiz/ord) |
|---|---|---|---|
| two-region spec over two groups | true | true | true |
| nested groups in a region | true | true | true |
| empty (solo box, no sets) | true | true | true |
| self-loop in a region of groups | true | true | true |
| zero-size fixed boxes in groups | true | true | true |
| ill-formed (dangling parent) | prefix fails | prefix fails | prefix fails |

The ill-formed input has `framedParents = false`, so it is outside the
residual premises (vacuous there); its prefix failure is expected and is not
a counterexample. All in-scope inputs satisfy every conjunct.
-/

/-- Region nesting allocation core: the `crossCoordsR` remainder shared by
both region residuals. Correspondence is the same-index proper-node
clusterPath fact; nesting transitivity lifts child-decl membership to the
parent decl; side existence keeps the child hulls nonempty; per-side
horizontal inclusion and member-vs-marker ordering are the allocation
horizontal facts from which both x-brackets follow by hull assembly. -/
def R_RegionNestAllocCore (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (spec' : Option RegionSpec) (cg' : Graph)
    (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg', run) →
    (∀ (index : Nat) (node : Node),
      (componentCandidateR spec' execution.graph comp candidate).nodes[index]? =
        some node →
      node.border = 0 ∨ node.border = -2 →
      ∃ actual : ProperNode, run.proper.nodes[index]? = some actual ∧
        actual.node.clusterPath = node.clusterPath) ∧
    (∀ (parentIndex childIndex : Nat) (parent child : Node)
      (parentBox childBox : ModelBox),
      (componentCandidateR spec' execution.graph comp candidate).nodes[parentIndex]? =
        some parent →
      parent.border = -2 →
      (componentCandidateR spec' execution.graph comp candidate).nodes[childIndex]? =
        some child →
      child.border = -2 →
      inp.boxes[parent.decl]? = some parentBox →
      inp.boxes[child.decl]? = some childBox →
      childBox.parent = parentBox.id → childBox.parent ≠ "" →
      (∀ (e : ProperNode × Nat), e ∈ run.proper.nodes.zipIdx →
        e.1.node.clusterPath.contains child.decl = true →
        e.1.node.clusterPath.contains parent.decl = true) ∧
      (∃ (sideIndex : Nat) (side : ProperNode),
        run.proper.nodes[sideIndex]? = some side ∧
        (side.node.border = -1 ∨ side.node.border = 1) ∧
        side.node.clusterPath.getLast? = some child.decl) ∧
      (∀ (e : ProperNode × Nat), e ∈ run.proper.nodes.zipIdx →
        (e.1.node.border = -1 ∨ e.1.node.border = 1) →
        e.1.node.clusterPath.getLast? = some child.decl →
        (frameRect execution.params
          (componentCandidateR spec' execution.graph comp candidate)
          run parentIndex).x ≤ (Labels.rectAt run.proper run.xs run.ys e.2).x ∧
        (Labels.rectAt run.proper run.xs run.ys e.2).x +
          (Labels.rectAt run.proper run.xs run.ys e.2).w ≤
          (frameRect execution.params
            (componentCandidateR spec' execution.graph comp candidate)
            run parentIndex).x +
          (frameRect execution.params
            (componentCandidateR spec' execution.graph comp candidate)
            run parentIndex).w)) ∧
    (∀ (index memberIndex : Nat) (node member : Node),
      (componentCandidateR spec' execution.graph comp candidate).nodes[index]? =
        some node →
      node.border = -2 →
      (componentCandidateR spec' execution.graph comp candidate).nodes[memberIndex]? =
        some member →
      member.border = 0 → member.clusterPath.contains node.decl = true →
      (run.proper.nodes[memberIndex]?.isSome = true) ∧
      ∃ (li ri : Nat) (l r : ProperNode),
        run.proper.nodes[li]? = some l ∧
        run.proper.nodes[ri]? = some r ∧
        (l.node.border = -1 ∨ l.node.border = 1) ∧
        (r.node.border = -1 ∨ r.node.border = 1) ∧
        l.node.clusterPath.getLast? = some node.decl ∧
        r.node.clusterPath.getLast? = some node.decl ∧
        (Labels.rectAt run.proper run.xs run.ys li).x ≤
          (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
          (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
          (Labels.rectAt run.proper run.xs run.ys ri).x +
          (Labels.rectAt run.proper run.xs run.ys ri).w)
/-- Plain member frames are their proper rects. -/
private theorem rnfp_memberFrameEq (P : Params) (cg : Graph) (run : Run)
    {memberIndex : Nat} {member : Node} {actual : ProperNode}
    (hmemberGet : cg.nodes.getD memberIndex default = member)
    (hplain : member.border = 0)
    (hproper : run.proper.nodes[memberIndex]? = some actual) :
    frameRect P cg run memberIndex =
      Labels.rectAt run.proper run.xs run.ys memberIndex := by
  unfold frameRect
  rw [hmemberGet]
  simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
  unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
    RouteImpl.nodeW RouteImpl.nodeH
  simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]

/-- Side-marker hull set for one group decl. -/
private def rnfp_parentBorders (run : Run) (decl : Nat) : List Rect :=
  run.proper.nodes.zipIdx.filterMap fun entry =>
    if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
        entry.1.node.clusterPath.getLast? == some decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none

/-- Member hull set for one group decl. -/
private def rnfp_memberRects (run : Run) (decl : Nat) : List Rect :=
  run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none

/-- Parent side markers lie in the parent frame. -/
private theorem rnfp_parentMarkerContained (P : Params) (cg : Graph) (run : Run)
    {i li : Nat} {parent : Node} {mk : ProperNode}
    (hparentGet : cg.nodes.getD i default = parent)
    (hparentGroup : parent.border = -2)
    (hq : (mk, li) ∈ run.proper.nodes.zipIdx)
    (hb : mk.node.border = -1 ∨ mk.node.border = 1)
    (hlast : mk.node.clusterPath.getLast? = some parent.decl) :
    (frameRect P cg run i).Contained (Labels.rectAt run.proper run.xs run.ys li) := by
  have hmemB : Labels.rectAt run.proper run.xs run.ys li ∈
      rnfp_parentBorders run parent.decl := by
    unfold rnfp_parentBorders
    apply List.mem_filterMap.mpr
    refine ⟨(mk, li), hq, ?_⟩
    rcases hb with hb | hb <;> simp [hb, hlast]
  have hcontains : mk.node.clusterPath.contains parent.decl = true :=
    List.contains_iff_mem.mpr (List.mem_of_getLast? hlast)
  have hborder : (cg.nodes.getD i default).border = -2 := by
    rw [hparentGet]; exact hparentGroup
  have hcontains' : mk.node.clusterPath.contains (cg.nodes.getD i default).decl = true := by
    rw [hparentGet]; exact hcontains
  have hvert := frameRect_member_vertical (P := P) (cg := cg) (run := run)
    (i := i) (q := (mk, li)) hborder hq hcontains'
  have hlo := boundsOf_minX_le_rect_x _ [] _ hmemB
  have hhi := rect_right_le_boundsOf_right _ [] _ hmemB
  have hx : (frameRect P cg run i).x = (boundsOf (rnfp_parentBorders run parent.decl) []).minX := by
    simp only [frameRect, hparentGet, hparentGroup, rnfp_parentBorders,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hr : (frameRect P cg run i).x + (frameRect P cg run i).w =
      (boundsOf (rnfp_parentBorders run parent.decl) []).right := by
    simp only [frameRect, hparentGet, hparentGroup, rnfp_parentBorders,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega
  unfold Rect.Contained
  exact ⟨hx.symm ▸ hlo, hr.symm ▸ hhi, hvert.1, hvert.2⟩

/-- The plain-member x-bracket from the allocation core. -/
theorem R_regionNestSomeResidual_of_allocCore {exactIds : List String}
    {idSets : List (String × List String)}
    (hcore : R_RegionNestAllocCore exactIds idSets) :
    R_RegionNestSomeResidual exactIds idSets := by
  intro inp o res execution hwf hframed comp candidate spec' cg' run orderOptions
    _hspec hcomp hrun index memberIndex node member hnode hgroup hmember hplain hinside
  obtain ⟨hcorr, -, hrect⟩ :=
    hcore execution hwf hframed comp candidate spec' cg' run orderOptions hcomp hrun
  obtain ⟨actual, hproper, hactualPath⟩ := hcorr memberIndex member hmember (Or.inl hplain)
  obtain ⟨-, li, ri, l, r, hli, hri, hlb, hrb, hllast, hrlast, hordL, hordR⟩ :=
    hrect index memberIndex node member hnode hgroup hmember hplain hinside
  have hparentGet : (componentCandidateR spec' execution.graph comp candidate).nodes.getD
      index default = node := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hqL : (l, li) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hli
  have hqR : (r, ri) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hri
  have hcontL := rnfp_parentMarkerContained execution.params _ run hparentGet hgroup
    hqL hlb hllast
  have hcontR := rnfp_parentMarkerContained execution.params _ run hparentGet hgroup
    hqR hrb hrlast
  refine ⟨actual, hproper, hactualPath,
    Int.le_trans hcontL.1 hordL, Int.le_trans hordR hcontR.2.1⟩



/-- Rect hulls have nonnegative right extent. -/
private theorem rnfp_hull_right_nonneg (rects : List Rect) :
    0 ≤ (boundsOf rects []).right := by
  cases rects with
  | nil => exact Int.le_refl 0
  | cons first rest =>
    change 0 ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).right
    exact foldl_stepRect_le_right _ _

/-- Rect hulls have nonnegative bottom extent. -/
private theorem rnfp_hull_bottom_nonneg (rects : List Rect) :
    0 ≤ (boundsOf rects []).bottom := by
  cases rects with
  | nil => exact Int.le_refl 0
  | cons first rest =>
    change 0 ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).bottom
    exact foldl_stepRect_le_bottom _ _

/-- Rect hulls preserve horizontal bounds. -/
private theorem rnfp_hull_horizontal (rects : List Rect) (lo hi : Int)
    (hne : rects ≠ []) (hhi : 0 ≤ hi)
    (hrects : ∀ rect ∈ rects, lo ≤ rect.x ∧ rect.x + rect.w ≤ hi) :
    lo ≤ (boundsOf rects []).minX ∧ (boundsOf rects []).right ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minX → initial.right ≤ hi →
      (∀ rect ∈ remaining, lo ≤ rect.x ∧ rect.x + rect.w ≤ hi) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minX ∧
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).right ≤ hi := by
    intro remaining
    induction remaining with
    | nil =>
      intro initial hlo hupper _
      exact ⟨hlo, hupper⟩
    | cons first rest ih =>
      intro initial hlo hupper hall
      simp only [List.foldl_cons]
      apply ih
      · exact Int.le_min.mpr ⟨hlo, (hall first (by simp)).1⟩
      · exact Int.max_le.mpr ⟨hupper, (hall first (by simp)).2⟩
      · intro rect hr
        exact hall rect (List.mem_cons_of_mem _ hr)
  cases rects with
  | nil => exact (hne rfl).elim
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minX ∧ _
    exact preserve _ _ (hrects first (by simp)).1 hhi hrects

/-- Rect hulls preserve vertical bounds. -/
private theorem rnfp_hull_vertical (rects : List Rect) (lo hi : Int)
    (hne : rects ≠ []) (hhi : 0 ≤ hi)
    (hrects : ∀ rect ∈ rects, lo ≤ rect.y ∧ rect.y + rect.h ≤ hi) :
    lo ≤ (boundsOf rects []).minY ∧ (boundsOf rects []).bottom ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minY → initial.bottom ≤ hi →
      (∀ rect ∈ remaining, lo ≤ rect.y ∧ rect.y + rect.h ≤ hi) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minY ∧
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).bottom ≤ hi := by
    intro remaining
    induction remaining with
    | nil =>
      intro initial hlo hupper _
      exact ⟨hlo, hupper⟩
    | cons first rest ih =>
      intro initial hlo hupper hall
      simp only [List.foldl_cons]
      apply ih
      · exact Int.le_min.mpr ⟨hlo, (hall first (by simp)).1⟩
      · exact Int.max_le.mpr ⟨hupper, (hall first (by simp)).2⟩
      · intro rect hr
        exact hall rect (List.mem_cons_of_mem _ hr)
  cases rects with
  | nil => exact (hne rfl).elim
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minY ∧ _
    exact preserve _ _ (hrects first (by simp)).1 hhi hrects
/-- Child-group frames lie in their parent frame, from the allocation core. -/
theorem R_regionNestGroupResidual_of_allocCore {exactIds : List String}
    {idSets : List (String × List String)}
    (hcore : R_RegionNestAllocCore exactIds idSets) :
    R_RegionNestGroupResidual exactIds idSets := by
  intro inp o res execution hwf hframed comp candidate spec' cg' run orderOptions
    hcomp hrun parentIndex childIndex parent child hparent hpgroup hchild hcgroup
    parentBox childBox hparentBox hchildBox hparentRef hparentNe
  obtain ⟨-, hgroup, -⟩ :=
    hcore execution hwf hframed comp candidate spec' cg' run orderOptions hcomp hrun
  obtain ⟨hnest, hexist, hside⟩ :=
    hgroup parentIndex childIndex parent child parentBox childBox
      hparent hpgroup hchild hcgroup hparentBox hchildBox hparentRef hparentNe
  have hparentGet : (componentCandidateR spec' execution.graph comp candidate).nodes.getD
      parentIndex default = parent := by
    simp only [List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hchildGet : (componentCandidateR spec' execution.graph comp candidate).nodes.getD
      childIndex default = child := by
    simp only [List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hborderP : ((componentCandidateR spec' execution.graph comp candidate).nodes.getD
      parentIndex default).border = -2 := by
    rw [hparentGet]; exact hpgroup
  have hxP : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).x =
      (boundsOf (rnfp_parentBorders run parent.decl) []).minX := by
    simp only [frameRect, hparentGet, hpgroup, rnfp_parentBorders,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hrP : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).x +
      (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).w =
      (boundsOf (rnfp_parentBorders run parent.decl) []).right := by
    simp only [frameRect, hparentGet, hpgroup, rnfp_parentBorders,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega
  have hyP : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).y =
      (boundsOf (rnfp_memberRects run parent.decl) []).minY := by
    simp only [frameRect, hparentGet, hpgroup, rnfp_memberRects,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hbP : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).y +
      (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).h =
      (boundsOf (rnfp_memberRects run parent.decl) []).bottom := by
    simp only [frameRect, hparentGet, hpgroup, rnfp_memberRects,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega
  have hxC : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run childIndex).x =
      (boundsOf (rnfp_parentBorders run child.decl) []).minX := by
    simp only [frameRect, hchildGet, hcgroup, rnfp_parentBorders,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hrC : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run childIndex).x +
      (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run childIndex).w =
      (boundsOf (rnfp_parentBorders run child.decl) []).right := by
    simp only [frameRect, hchildGet, hcgroup, rnfp_parentBorders,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega
  have hyC : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run childIndex).y =
      (boundsOf (rnfp_memberRects run child.decl) []).minY := by
    simp only [frameRect, hchildGet, hcgroup, rnfp_memberRects,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hbC : (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run childIndex).y +
      (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run childIndex).h =
      (boundsOf (rnfp_memberRects run child.decl) []).bottom := by
    simp only [frameRect, hchildGet, hcgroup, rnfp_memberRects,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega
  obtain ⟨swi, sw, hsw, hswb, hswlast⟩ := hexist
  have hswmem : (sw, swi) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hsw
  have hswcontains : sw.node.clusterPath.contains child.decl = true :=
    List.contains_iff_mem.mpr (List.mem_of_getLast? hswlast)
  have hmemSides : Labels.rectAt run.proper run.xs run.ys swi ∈
      rnfp_parentBorders run child.decl := by
    unfold rnfp_parentBorders
    apply List.mem_filterMap.mpr
    refine ⟨(sw, swi), hswmem, ?_⟩
    rcases hswb with hb | hb <;> simp [hb, hswlast]
  have hmemRects : Labels.rectAt run.proper run.xs run.ys swi ∈
      rnfp_memberRects run child.decl := by
    unfold rnfp_memberRects
    apply List.mem_filterMap.mpr
    refine ⟨(sw, swi), hswmem, ?_⟩
    simp only [hswcontains, ↓reduceIte]
  have hneS : rnfp_parentBorders run child.decl ≠ [] := by
    intro hempty
    rw [hempty] at hmemSides
    exact List.not_mem_nil hmemSides
  have hneR : rnfp_memberRects run child.decl ≠ [] := by
    intro hempty
    rw [hempty] at hmemRects
    exact List.not_mem_nil hmemRects
  have hallX : ∀ rect ∈ rnfp_parentBorders run child.decl,
      (frameRect execution.params
        (componentCandidateR spec' execution.graph comp candidate) run parentIndex).x ≤
        rect.x ∧
      rect.x + rect.w ≤
        (frameRect execution.params
        (componentCandidateR spec' execution.graph comp candidate) run parentIndex).x +
        (frameRect execution.params
        (componentCandidateR spec' execution.graph comp candidate) run parentIndex).w := by
    intro rect hrect
    unfold rnfp_parentBorders at hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcond
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      have hb : entry.1.node.border = -1 ∨ entry.1.node.border = 1 := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using (Bool.and_eq_true_iff.mp hcond).1
      have hll : entry.1.node.clusterPath.getLast? = some child.decl :=
        beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2
      exact hside entry hentry hb hll
    · cases heq
  have hallY : ∀ rect ∈ rnfp_memberRects run child.decl,
      (frameRect execution.params
        (componentCandidateR spec' execution.graph comp candidate) run parentIndex).y ≤
        rect.y ∧
      rect.y + rect.h ≤
        (frameRect execution.params
        (componentCandidateR spec' execution.graph comp candidate) run parentIndex).y +
        (frameRect execution.params
        (componentCandidateR spec' execution.graph comp candidate) run parentIndex).h := by
    intro rect hrect
    unfold rnfp_memberRects at hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcond
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      have hcc : entry.1.node.clusterPath.contains child.decl = true := hcond
      have hpar : entry.1.node.clusterPath.contains parent.decl = true :=
        hnest entry hentry hcc
      have hpar' : entry.1.node.clusterPath.contains
          ((componentCandidateR spec' execution.graph comp candidate).nodes.getD
            parentIndex default).decl = true := by
        rw [hparentGet]; exact hpar
      exact frameRect_member_vertical (i := parentIndex) (q := entry) hborderP hentry hpar'
    · cases heq
  have hhiX : 0 ≤ (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).x +
      (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).w := by
    rw [hrP]; exact rnfp_hull_right_nonneg _
  have hhiY : 0 ≤ (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).y +
      (frameRect execution.params
      (componentCandidateR spec' execution.graph comp candidate) run parentIndex).h := by
    rw [hbP]; exact rnfp_hull_bottom_nonneg _
  have hXt := rnfp_hull_horizontal (rnfp_parentBorders run child.decl) _ _ hneS hhiX hallX
  have hYt := rnfp_hull_vertical (rnfp_memberRects run child.decl) _ _ hneR hhiY hallY
  unfold Rect.Contained
  rw [hrC, hbC, hxC, hyC]
  exact ⟨hXt.1, hXt.2, hYt.1, hYt.2⟩
end PipelineImpl
end Layered
end Elegant
