import Elegant.Layered.ExpandChildFrameLiftProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.SelectFacts
import Elegant.Layered.MergedRouteIdsProof
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.RecursiveFit
 import Elegant.Layered.ExpandChildContainment
 import Elegant.Layered.InsetFit
 import Elegant.Layered.ExpandChildChildSceneProof
 import Elegant.Layered.ExpandChildCanvasFitProof
 import Elegant.Layered.PolylineBoxMiss

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Residual discharges for `ExpandChildFrameLiftProof`.

Target theorems:
(1) `expandChildParentIsolated : ExpandChildParentIsolated group parent`
(2) `expandChildChildRouteParentFrame : ExpandChildChildRouteParentFrame ...`
(3) `expandChildParentRouteChildFrame : ExpandChildParentRouteChildFrame ...`

(1) is proved here (vendored ancestor-walk toolkit: the tracked
`ExpandChildAncestryProof` does not elaborate past its downstream section,
so its `expandChild_group_isolated` is re-established from the same lemmas).
-/

/-! ## Vendored ancestor-walk toolkit (cf. `ExpandChildAncestryProof`) -/

/-- A single-parent-step chain. -/
inductive IsoStepChain (R : String → String → Prop) : List String → Prop where
  | nil : IsoStepChain R []
  | single (a : String) : IsoStepChain R [a]
  | cons {a b : String} {rest : List String} :
    R a b → IsoStepChain R (b :: rest) → IsoStepChain R (a :: b :: rest)

/-- One unfolded step of the ancestor walk. -/
private theorem iso_go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- Membership in the ancestor walk exhibits a step chain. -/
private theorem iso_go_chain_of_mem {d : LayoutDump} :
    ∀ (K : Nat) (s x : String),
    x ∈ LayoutDump.ancestors.go d K s →
    ∃ c, IsoStepChain
      (fun s t => ∃ b, d.box? s = some b ∧ b.parent = t ∧ t ≠ "") c ∧
      c.head? = some s ∧ c.getLast? = some x ∧ c.length ≤ K + 1
  | 0, s, x, hx => by
    simp only [LayoutDump.ancestors.go] at hx
    cases hx
  | K + 1, s, x, hx => by
    cases h : d.box? s with
    | none =>
      have hfind : d.boxes.find? (fun b => b.id == s) = none := h
      simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind] at hx
      cases hx
    | some b =>
      have hfind : d.boxes.find? (fun b => b.id == s) = some b := h
      by_cases hpar : b.parent = ""
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar,
          ↓reduceIte] at hx
        cases hx
      · have hgo := iso_go_succ (d := d) (k := K) (s := s) (b := b) h hpar
        rw [hgo] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · refine ⟨[s, b.parent],
            IsoStepChain.cons ⟨b, h, rfl, hpar⟩ (IsoStepChain.single _),
            by simp, by simp, ?_⟩
          simp only [List.length_cons, List.length_nil]
          omega
        · obtain ⟨c', hchain', hhead', hlast', hlen'⟩ :=
            iso_go_chain_of_mem K b.parent x hx'
          obtain ⟨p', rest', hcsplit⟩ : ∃ p' rest', c' = p' :: rest' := by
            cases c' with
            | nil => simp at hhead'
            | cons p' rest' => exact ⟨p', rest', rfl⟩
          subst hcsplit
          have hpeq : p' = b.parent := by simpa using hhead'
          subst hpeq
          refine ⟨s :: b.parent :: rest',
            IsoStepChain.cons ⟨b, h, rfl, hpar⟩ hchain',
            by simp, ?_, ?_⟩
          · have hgg : ((s :: b.parent :: rest').getLast? =
              (b.parent :: rest').getLast?) := rfl
            rw [hgg]
            exact hlast'
          · simp only [List.length_cons] at hlen' ⊢
            omega

/-- The last link of a step chain whose ends differ ends at the last element. -/
private theorem iso_stepChain_last_link {R : String → String → Prop}
    {c : List String} {s x : String}
    (hchain : IsoStepChain R c) (hhead : c.head? = some s)
    (hlast : c.getLast? = some x) (hne : s ≠ x) :
    ∃ y, R y x ∧ y ∈ c := by
  induction hchain generalizing s x with
  | nil => simp at hhead
  | single a =>
    have hs : a = s := by simpa using hhead
    have hx : a = x := by simpa using hlast
    exact absurd (hs.symm.trans hx) hne
  | cons hab htail ih =>
    rename_i a b rest
    have hlast' : (b :: rest).getLast? = some x := hlast
    by_cases hbx : b = x
    · exact ⟨a, hbx ▸ hab, List.mem_cons.mpr (Or.inl rfl)⟩
    · obtain ⟨y, hry, hym⟩ := ih (by simp) hlast' hbx
      exact ⟨y, hry, List.mem_cons.mpr (Or.inr hym)⟩

/-- The ancestor walk from a missing id is empty. -/
private theorem iso_empty_not_mem_ancestors_go {d : LayoutDump}
    (k : Nat) (s : String) :
    "" ∉ LayoutDump.ancestors.go d k s := by
  revert s
  induction k with
  | zero =>
    intro s hmem
    cases hmem
  | succ k ih =>
    intro s hmem
    simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hmem
    match h : d.boxes.find? (fun b => b.id == s) with
    | none =>
      simp only [h] at hmem
      cases hmem
    | some b =>
      simp only [h] at hmem
      by_cases hp : b.parent = ""
      · simp only [hp, ↓reduceIte] at hmem
        cases hmem
      · simp only [hp, ↓reduceIte, List.mem_cons] at hmem
        have hne : ("" : String) ≠ b.parent := Ne.symm hp
        have hmem' : "" ∈ LayoutDump.ancestors.go d k b.parent := by
          rcases hmem with hcontra | hrest
          · exact absurd hcontra hne
          · exact hrest
        exact ih _ hmem'

private theorem iso_empty_not_mem_ancestors {d : LayoutDump} (s : String) :
    "" ∉ d.ancestors s := by
  unfold LayoutDump.ancestors
  exact iso_empty_not_mem_ancestors_go d.boxes.length s

/-- (1) proved: parent isolation is group isolation, re-established here. -/
theorem expandChildParentIsolated
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildParentIsolated group parent := by
  obtain ⟨hwf, hgroup, hpboxes, _, hparent, _⟩ := hctx
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hgsel : group ∈ inp.boxes := List.mem_of_find?_eq_some hgroup
  have hpnodup : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hnodup
  intro pb hpb hne
  by_cases hg : group.id = ""
  · rw [hg]
    exact iso_empty_not_mem_ancestors pb.id
  · intro hmem
    have hxgo : group.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        parent.scene.layoutDump.boxes.length pb.id := hmem
    obtain ⟨c₂, hchain₂, hhead₂, hlast₂, _hlen₂⟩ :=
      iso_go_chain_of_mem _ _ _ hxgo
    obtain ⟨y, hry, _hym⟩ :=
      iso_stepChain_last_link hchain₂ hhead₂ hlast₂ hne
    obtain ⟨bb, hbbhit, hbbpar, _hbbne⟩ := hry
    have hbbmem : bb ∈ parent.scene.boxes :=
      List.mem_of_find?_eq_some hbbhit
    obtain ⟨sb, hsbmem, _hsbid, hsbpar⟩ :=
      layoutRecursive_scene_box_parent fuel _ _ _ hpnodup hparent bb hbbmem
    rw [hpboxes] at hsbmem
    obtain ⟨m, hmmem, hkeep, _, hmsbpar⟩ :=
      selectInput_box_spec inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
    have hsbpar' : sb.parent = group.id := by
      rw [← hsbpar]
      exact hbbpar
    have hmpar : m.parent = group.id := by
      rw [hmsbpar] at hsbpar'
      by_cases he : m.parent = ""
      · rw [he] at hsbpar' ⊢
        simpa using hsbpar'
      · have hcond : (m.parent == "") = false := by
          cases hbe : (m.parent == "") with
          | true => exact absurd (beq_iff_eq.mp hbe) he
          | false => rfl
        simpa [hcond] using hsbpar'
    have hmne : m.parent ≠ "" := by
      rw [hmpar]
      exact hg
    have hin : Compound.inside inp.boxes group.id m.id = true :=
      inside_of_parent hnodup hgsel hmmem hmpar.symm hmne
    have hcontra : ¬ ((!true : Bool) = true) := by decide
    rw [hin] at hkeep
    exact hcontra hkeep
 /-! ## Narrowed residual for the child-route / parent-frame cross case -/

 /-- One parent-scene fact: a parent-located frame is disjoint from the
 group frame, and the group frame is nondegenerate. Strictly simpler than
 `ExpandChildChildRouteParentFrame` (two rects, no routes, no merge). -/
 def ExpandChildParentFixedDisjointGroup (frame gFrame : Box) : Prop :=
   Disjoint frame.rect gFrame.rect ∧ 0 < frame.rect.w ∧ 0 < frame.rect.h

 /-- Strict containment weakens to containment. -/
 private theorem strictInside_to_contained {outer inner : Rect}
     (h : outer.StrictInside inner) : outer.Contained inner := by
   simp only [Rect.StrictInside, Rect.Contained] at h ⊢
   omega

 /-- (2) narrowed: a shifted child route misses a disjoint parent frame. -/
 theorem expandChildChildRouteParentFrame_of_disjoint
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child result : FamilyResult}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok result)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child result)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
     {_g : ModelBox}
     (_hgEx : ∃ _entry : String × Size,
       inp.fixedSizes.find? (fun fixed => fixed.1 == _g.id) = some _entry)
     {gFrame : Box}
     (_hfindG : parent.scene.boxes.find? (fun box => box.id == _g.id) = some gFrame)
     {frame : Box}
     {titleLines₀ : List Measure.Line} {dx dy : Int}
     (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
     (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
         (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).x -
       P.canvasMargin)
     (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
         (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).y -
       P.canvasMargin)
     (hwrap : ExpandChildTitleWrapped P inp o group titleLines₀)
     (hdisj : ExpandChildParentFixedDisjointGroup frame gFrame)
     {cr : Route} (hcr : cr ∈ child.scene.routes)
     (_hfrom : cr.fromId ≠ _g.id) (_hto : cr.toId ≠ _g.id)
     (_hscope : _g.id ∉ LayoutDump.routeScope result.scene.layoutDump cr) :
     ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) gFrame.rect := by
   have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
   have hconf : ∀ p ∈ cr.points.map (shiftPoint dx dy),
       PointIn frame.rect p := by
     intro p hp
     obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
     have hqI := expandChild_child_routes_inset fuel P inp o group titleLines
       titleHeight parent child result hexpand hframed hctx hP cr hcr q hq
     have hqs := pointIn_shift (dx := dx) (dy := dy) hqI
     have hrefl : (insetRect child.scene.canvas P.canvasMargin).Contained
         (insetRect child.scene.canvas P.canvasMargin) := by
       unfold insetRect Rect.Contained
       exact ⟨by omega, by omega, by omega, by omega⟩
     have hSI := expandChild_content_fit_strict fuel P inp o group titleLines
       titleHeight parent child result hexpand hframed hctx hparams frame
       titleLines₀ dx dy hframe hdx hdy hwrap _ hrefl
     have hC := strictInside_to_contained hSI
     have hdeg := pointIn_contained.mp hqs
     have hfp := Rect.Contained.trans hC hdeg
     exact pointIn_contained.mpr hfp
   obtain ⟨hdisjD, hfw, hfh⟩ := hdisj
   exact polyline_in_box_misses_disjoint hfw hfh hconf hdisjD

 /-! ## Narrowed residual for the parent-route / child-frame cross case -/

 /-- One parent-scene fact: every parent route misses every rectangle
 strictly inside the group frame. Strictly simpler than
 `ExpandChildParentRouteChildFrame` (one scene, no child, no merge). -/
 def ExpandChildParentStrictMissGroup (group : ModelBox)
     (parent : FamilyResult) : Prop :=
   ∀ (frame : Box),
     parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
     ∀ pr ∈ parent.scene.routes, ∀ (r : Rect),
       frame.rect.StrictInside r →
       ¬ Polyline.hitsRect pr.points r

 /-- (3) narrowed: a parent route misses a shifted child frame. -/
 theorem expandChildParentRouteChildFrame_of_strictMiss
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child result : FamilyResult}
     (hexpand : expandChild P inp o group titleHeight parent child = .ok result)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child result)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
     {_g : ModelBox}
     (_hgEx : ∃ _entry : String × Size,
       inp.fixedSizes.find? (fun fixed => fixed.1 == _g.id) = some _entry)
     {gFrame : Box}
     (_hfindR : result.scene.boxes.find? (fun box => box.id == _g.id) = some gFrame)
     {cb : Box}
     (hcb : child.scene.boxes.find? (fun box => box.id == _g.id) = some cb)
     {frame : Box}
     {titleLines₀ : List Measure.Line} {dx dy : Int}
     (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
     (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
         (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).x -
       P.canvasMargin)
     (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
         (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).y -
       P.canvasMargin)
     (hwrap : ExpandChildTitleWrapped P inp o group titleLines₀)
     (hmiss : ExpandChildParentStrictMissGroup group parent)
     (_hgEmb : gFrame = embedBox group.id dx dy cb)
     {pr : Route} (hpr : pr ∈ parent.scene.routes)
     (_hfrom : pr.fromId ≠ _g.id) (_hto : pr.toId ≠ _g.id)
     (_hscope : _g.id ∉ LayoutDump.routeScope result.scene.layoutDump pr) :
     ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect) := by
   have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
   have hcbmem : cb ∈ child.scene.boxes := List.mem_of_find?_eq_some hcb
   have hcbI := expandChild_child_boxes_inset fuel P inp o group titleLines
     titleHeight parent child result hexpand hframed hctx hP cb hcbmem
   have hSI := expandChild_content_fit_strict fuel P inp o group titleLines
     titleHeight parent child result hexpand hframed hctx hparams frame
     titleLines₀ dx dy hframe hdx hdy hwrap cb.rect hcbI
   exact hmiss frame hframe pr hpr (shiftRect dx dy cb.rect) hSI
 /-! ## Restated lifts with the three residuals discharged -/

 /-- The frame-clear lift with the cross-side residuals replaced by the two
 narrowed parent-scene wrappers (isolation is proved above). -/
 theorem layoutRecursive_frame_clear'
     (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → FrameClearanceSeam inp o res)
     (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → ExclusiveRunNodeDecl inp o res)
     (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → RunRouteEndpointIdsScoped inp o res)
     (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → RoutePartShelfPositive inp o res)
     (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult) (execution : SceneExecution inp o res), WellFormed (inputModel inp o) → framedParents inp = true → ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat), comp ∈ components execution.graph → componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured (candidateOrder candidate) = .ok run → LoopReservation (componentCandidate execution.graph comp candidate) run execution.measured v)
     (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult) (execution : SceneExecution inp o res), WellFormed (inputModel inp o) → framedParents inp = true → ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat), comp ∈ components execution.graph → ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 → componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured (candidateOrder candidate) = .ok run → LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run execution.measured v b)
     (hsub : SubInputWellFormed)
     (hfixedDisj : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult) (g : ModelBox) (gFrame frame : Box), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → (∃ entry : String × Size, inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) → parent.scene.boxes.find? (fun box => box.id == g.id) = some gFrame → parent.scene.boxes.find? (fun box => box.id == group.id) = some frame → ExpandChildParentFixedDisjointGroup frame gFrame)
     (hstrictMiss : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildParentStrictMissGroup group parent) :
     ∀ (fuel : Nat) (inp : Input) (o : Options) (g : ModelBox) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → (∃ entry : String × Size, inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) → layoutRecursive fuel inp o = .ok res → ∀ (frame : Box), res.scene.boxes.find? (fun box => box.id == g.id) = some frame → ∀ r ∈ res.scene.routes, r.fromId ≠ g.id → r.toId ≠ g.id → g.id ∉ LayoutDump.routeScope res.scene.layoutDump r → ¬ Polyline.hitsRect r.points frame.rect := by
   have hcC : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight parent child res := by
     intro fuel P inp o group titleLines titleHeight parent child res _hexpand _hframed _hctx _hparams
     intro hexpand hframed hctx hparams g hgEx gFrame hfindG frame _metric _titleLines₀ _dx _dy hframe _hmetric _htitle hdx hdy hwrap cr hcr hfrom hto hscope
     exact expandChildChildRouteParentFrame_of_disjoint hexpand hframed hctx hparams hgEx hfindG hframe hdx hdy hwrap (hfixedDisj fuel P inp o group titleLines titleHeight parent child res g gFrame frame hexpand hframed hctx hparams hgEx hfindG hframe) hcr hfrom hto hscope
   have hpC : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildParentRouteChildFrame fuel P inp o group titleLines titleHeight parent child res := by
     intro fuel P inp o group titleLines titleHeight parent child res _hexpand _hframed _hctx _hparams
     intro hexpand hframed hctx hparams _g hgEx _gFrame hfindR _cb hcb _frame _metric _titleLines₀ _dx _dy hframe _hmetric _htitle hdx hdy hwrap hgEmb pr hpr hfrom hto hscope
     exact expandChildParentRouteChildFrame_of_strictMiss hexpand hframed hctx hparams hgEx hfindR hcb hframe hdx hdy hwrap (hstrictMiss fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams) hgEmb hpr hfrom hto hscope
   exact layoutRecursive_frame_clear hclear hnodeDecl hscoped hpos hloopRes hloopSep hsub hcC hpC

 /-- The executed-call parent-route frame clearance with the cross-side
 residuals replaced by the two narrowed wrappers (isolation proved above). -/
 theorem expandChild_parentRouteFrameClear'
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → FrameClearanceSeam inp o res)
     (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → ExclusiveRunNodeDecl inp o res)
     (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → RunRouteEndpointIdsScoped inp o res)
     (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult), WellFormed (inputModel inp o) → framedParents inp = true → RoutePartShelfPositive inp o res)
     (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult) (execution : SceneExecution inp o res), WellFormed (inputModel inp o) → framedParents inp = true → ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat), comp ∈ components execution.graph → componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured (candidateOrder candidate) = .ok run → LoopReservation (componentCandidate execution.graph comp candidate) run execution.measured v)
     (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult) (execution : SceneExecution inp o res), WellFormed (inputModel inp o) → framedParents inp = true → ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat), comp ∈ components execution.graph → ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 → componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured (candidateOrder candidate) = .ok run → LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run execution.measured v b)
     (hsub : SubInputWellFormed)
     (hfixedDisj : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult) (g : ModelBox) (gFrame frame : Box), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → (∃ entry : String × Size, inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) → parent.scene.boxes.find? (fun box => box.id == g.id) = some gFrame → parent.scene.boxes.find? (fun box => box.id == group.id) = some frame → ExpandChildParentFixedDisjointGroup frame gFrame)
     (hstrictMiss : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildParentStrictMissGroup group parent)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
     ExpandChildParentRouteFrameClear group parent := by
   have hcC : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight parent child res := by
     intro fuel P inp o group titleLines titleHeight parent child res _hexpand _hframed _hctx _hparams
     intro hexpand hframed hctx hparams g hgEx gFrame hfindG frame _metric _titleLines₀ _dx _dy hframe _hmetric _htitle hdx hdy hwrap cr hcr hfrom hto hscope
     exact expandChildChildRouteParentFrame_of_disjoint hexpand hframed hctx hparams hgEx hfindG hframe hdx hdy hwrap (hfixedDisj fuel P inp o group titleLines titleHeight parent child res g gFrame frame hexpand hframed hctx hparams hgEx hfindG hframe) hcr hfrom hto hscope
   have hpC : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult), expandChild P inp o group titleHeight parent child = .ok res → framedParents inp = true → ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res → ExpandChildCallParams P inp o group titleLines titleHeight → ExpandChildParentRouteChildFrame fuel P inp o group titleLines titleHeight parent child res := by
     intro fuel P inp o group titleLines titleHeight parent child res _hexpand _hframed _hctx _hparams
     intro hexpand hframed hctx hparams _g hgEx _gFrame hfindR _cb hcb _frame _metric _titleLines₀ _dx _dy hframe _hmetric _htitle hdx hdy hwrap hgEmb pr hpr hfrom hto hscope
     exact expandChildParentRouteChildFrame_of_strictMiss hexpand hframed hctx hparams hgEx hfindR hcb hframe hdx hdy hwrap (hstrictMiss fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams) hgEmb hpr hfrom hto hscope
   have hexpandC : expandChild P inp o group titleHeight parent child = .ok res := hctx.2.2.2.2.2
   have hiso : ExpandChildParentIsolated group parent := expandChildParentIsolated hexpandC hframed hctx hparams
   exact expandChild_parentRouteFrameClear hclear hnodeDecl hscoped hpos hloopRes hloopSep hsub hcC hpC hiso hframed hctx hparams
 end PipelineImpl
 end Layered
 end Elegant
