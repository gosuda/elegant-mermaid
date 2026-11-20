import Elegant.Layered.LaneEndsPinEnds
import Elegant.Layered.LaneEndsPinPhases
import Elegant.Layered.LaneEndsPinPhaseApply
import Elegant.Layered.LaneEndsPinPhaseReroute

set_option autoImplicit false

/-! Executed-band ends for `pinBands`.

`pinBands_ends` quantifies its two open phases over arbitrary band lists.
Its proof instantiates both only at the executed axis and `layBands` list,
so the executed forms `lepePhaseApplyPinExec` / `lepePhaseRerouteExec`
suffice: `pinBands_ends_exec` replays that body. The tail phases
(restore / relocate / grow) are band-independent; their proofs are
prefixed copies (`lxe_`) of the private steps in `LaneEndsPinEnds`.
`pinBands_ends_exec_closed` closes the two Exec premises through the
residuals `lppaFrameTransportResidual` and `lepeRerouteFreshEndsExec`.
The apply Exec form carries one extra premise the universal lacks:
every scene box id is nonempty (`hNoEmpty`), needed by the frame-transport
case split; it is stated explicitly here. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Binding step of an `Except` computation (local copy). -/
private theorem lxe_bind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A satisfying member gives a `find?` witness. -/
private theorem lxe_find?_ex {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∃ a, a ∈ l ∧ p a = true) →
      ∃ a, l.find? p = some a := by
  intro l
  induction l with
  | nil => intro ⟨a, ha, _⟩; cases ha
  | cons x xs ih =>
    intro ⟨a, ha, hp⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [List.find?_cons]
      cases hpx : p a with
      | true => exact ⟨a, rfl⟩
      | false => rw [hpx] at hp; cases hp
    · obtain ⟨b, hb⟩ := ih ⟨a, ha', hp⟩
      rw [List.find?_cons]
      cases hpx : p x with
      | true => exact ⟨x, rfl⟩
      | false => exact ⟨b, hb⟩

/-- Injectivity on a nodup image list. -/
private theorem lxe_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
    {l : List α} (h : (l.map g).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hnot, htail⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨y, hy', hgx.symm⟩
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨x, hx', hgx⟩
      · exact ih htail hx' hy'

/-- First index carrying a satisfying element, with all earlier failing. -/
private theorem lxe_find?_idx {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a →
      ∃ j : Nat, l[j]? = some a ∧ p a = true ∧
        ∀ k, k < j → ∀ y, l[k]? = some y → p y = false := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons x xs ih =>
    intro a h
    rw [List.find?_cons] at h
    cases hpx : p x with
    | true =>
      simp [hpx] at h
      subst h
      refine ⟨0, rfl, hpx, ?_⟩
      intro k hk _ _
      simp at hk
    | false =>
      simp [hpx] at h
      obtain ⟨j, hjget, hjp, hj4⟩ := ih a h
      refine ⟨j + 1, ?_, hjp, ?_⟩
      · rw [List.getElem?_cons_succ]
        exact hjget
      · intro k hk y hy
        cases k with
        | zero =>
          rw [List.getElem?_cons_zero] at hy
          cases hy
          exact hpx
        | succ k' =>
          rw [List.getElem?_cons_succ] at hy
          exact hj4 k' (by omega) _ hy

/-- Box correspondence through a uniform shift, with `find?` and rect. -/
private theorem lxe_shiftAll_boxIdx {axis : Axis} {delta : Int} {s : Scene}
    {boxes : List Box}
    (hboxes : s.boxes.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError Box)) = .ok boxes)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    {id : String} {fb : Box} (hfb : s.boxes.find? (fun b => b.id == id) = some fb) :
    ∃ b0', (boxes.find? fun b => b.id == id) = some b0' ∧ b0'.id = fb.id ∧
      b0'.rect = axis.withStart fb.rect (axis.start fb.rect + delta) := by
  have hfbM : fb ∈ s.boxes := List.mem_of_find?_eq_some hfb
  have hspecB := mapM_except_spec _ s.boxes boxes hboxes
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfbM
  have hjL : j < s.boxes.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjB : j < boxes.length := by have := hspecB.1; omega
  obtain ⟨b0, b0', hb0, hb0', hfb0⟩ := hspecB.2 j hjL hjB
  have hb0e : b0 = fb := Option.some.inj (hb0.symm.trans hj)
  have hnodupB' : (boxes.map (·.id)).Nodup := by
    have hid : boxes.map (·.id) = s.boxes.map (·.id) :=
      (shiftBoxes_maps s.boxes axis delta boxes hboxes).2.1
    rw [hid]
    exact hnodupB
  obtain ⟨hid0, _, _, _, w0, hw0, hrect0, hval0⟩ := shiftBox_ok hfb0
  have hb0'mem : b0' ∈ boxes := List.mem_iff_getElem?.mpr ⟨j, hb0'⟩
  obtain ⟨_, _, hjpred, _⟩ := lxe_find?_idx _ _ _ hfb
  have hfbid : fb.id = id := beq_iff_eq.mp hjpred
  have hidF : b0'.id = id := by rw [hb0e] at hid0; rw [hid0, hfbid]
  have hpredF : (fun b : Box => b.id == id) b0' = true := beq_iff_eq.mpr hidF
  obtain ⟨dF, hfindF0⟩ := lxe_find?_ex (fun b : Box => b.id == id) _ ⟨b0', hb0'mem, hpredF⟩
  have hdFeq : dF = b0' := by
    apply lxe_nodup_map_inj (·.id) hnodupB'
    · exact List.mem_of_find?_eq_some hfindF0
    · exact hb0'mem
    · obtain ⟨_, _, hjpred2, _⟩ := lxe_find?_idx _ _ _ hfindF0
      have h2 := beq_iff_eq.mp hjpred2
      rw [← hidF] at h2
      exact h2
  have hfindF : (boxes.find? fun b => b.id == id) = some b0' := by
    rw [← hdFeq]
    exact hfindF0
  have hrectF : b0'.rect = axis.withStart fb.rect (axis.start fb.rect + delta) := by
    rw [hb0e] at hrect0 hval0 hw0
    rw [hrect0, hval0]
  exact ⟨b0', hfindF, by rw [hidF, hfbid], hrectF⟩

/-- Route index correspondence through a uniform shift. -/
private theorem lxe_shiftAll_routeIdx {axis : Axis} {delta : Int} {s : Scene}
    {routes : List Route}
    (hroutes : s.routes.mapM (fun r : Route => (do pure { r with points := ← r.points.mapM ((Move.constant delta).point axis) } : Except LayoutError Route)) = .ok routes)
    {r' : Route} (hr' : r' ∈ routes) :
    ∃ r ∈ s.routes, r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      ∃ pts, r'.points = pts ∧
        r.points.mapM ((Move.constant delta).point axis) = .ok pts := by
  have hspecR := mapM_except_spec _ s.routes routes hroutes
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr'
  have hiL : i < routes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hiS : i < s.routes.length := by omega
  obtain ⟨r, bR, haR, hbR, hfab⟩ := hspecR.2 i hiS hiL
  have hrBmem : r ∈ s.routes := List.mem_iff_getElem?.mpr ⟨i, haR⟩
  have hbRe : bR = r' := Option.some.inj (hbR.symm.trans hi)
  obtain ⟨pts, hpts, hrfl⟩ := lxe_bind hfab
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  refine ⟨r, hrBmem, ?_, ?_, ?_, pts, ?_, hpts⟩ <;> rw [← hbRe, ← hrfl]

/-- Last point through a `mapM` point move. -/
private theorem lxe_mapM_point_getLast {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.getLast? = some p →
        ∃ q, qs.getLast? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x rest ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := lxe_bind h
    obtain ⟨rest', hrest, hrfl⟩ := lxe_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    cases rest with
    | nil =>
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hrest
      subst hrest
      have hpx : p = x := by
        have hgl : (x :: []).getLast? = some x := rfl
        rw [hgl] at hp
        exact (Option.some.inj hp).symm
      subst hpx
      exact ⟨x', rfl, hx'⟩
    | cons y ys =>
      obtain ⟨q, hq, hfun⟩ := ih rest' hrest p hp
      refine ⟨q, ?_, hfun⟩
      rw [List.getLast?_cons, hq]
      rfl

/-- Head point through a `mapM` point move. -/
private theorem lxe_mapM_point_head {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.head? = some p →
        ∃ q, qs.head? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x xs ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := lxe_bind h
    obtain ⟨rest', hrest, hrfl⟩ := lxe_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    have hpx : x = p := by simpa using hp
    subst hpx
    exact ⟨x', rfl, hx'⟩

/-- A uniform cross shift commutes with `endRect`. -/
private theorem lxe_endRect_shift {axis : Axis} {frames : List LaneFrame}
    {b b' : Box} {delta : Int}
    (hrect : b'.rect = axis.withStart b.rect (axis.start b.rect + delta))
    (hid : b'.id = b.id) :
    endRect axis frames b' =
      axis.withStart (endRect axis frames b)
        (axis.start (endRect axis frames b) + delta) := by
  have hfind : (frames.find? fun b_ => b_.id == b'.id) =
      frames.find? fun b_ => b_.id == b.id := by rw [hid]
  unfold endRect
  rw [hfind]
  cases hf : frames.find? (fun b_ => b_.id == b.id) with
  | none =>
    exact hrect
  | some f =>
    cases axis with
    | x =>
      have hx : b'.rect.x = b.rect.x + delta := by rw [hrect]; rfl
      have hy : b'.rect.y = b.rect.y := by rw [hrect]; rfl
      have hw : b'.rect.w = b.rect.w := by rw [hrect]; rfl
      have hh : b'.rect.h = b.rect.h := by rw [hrect]; rfl
      simp only [oldFrame, placeRect, Axis.withStart, Axis.withLength,
        Axis.start, hx, hy, hw, hh]
      congr 1 <;> omega
    | y =>
      have hx : b'.rect.x = b.rect.x := by rw [hrect]; rfl
      have hy : b'.rect.y = b.rect.y + delta := by rw [hrect]; rfl
      have hw : b'.rect.w = b.rect.w := by rw [hrect]; rfl
      have hh : b'.rect.h = b.rect.h := by rw [hrect]; rfl
      simp only [oldFrame, placeRect, Axis.withStart, Axis.withLength,
        Axis.start, hx, hy, hw, hh]
      congr 1 <;> omega

/-- A uniform shift preserves `EndsOnOld`. -/
private theorem lxe_shiftAll_ends {axis : Axis} {delta : Int} {s s' : Scene}
    {frames : List LaneFrame}
    (h : shiftAll axis delta s = .ok s')
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hE : EndsOnOld axis frames s.layoutDump) :
    EndsOnOld axis frames s'.layoutDump := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h1⟩ := lxe_bind h
  obtain ⟨labels, hlabels, h2⟩ := lxe_bind h1
  obtain ⟨routes, hroutes, h3⟩ := lxe_bind h2
  obtain ⟨items, hitems, h4⟩ := lxe_bind h3
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h4
  subst h4
  intro r' hr'
  have hrM : r' ∈ routes := hr'
  obtain ⟨r, hrBmem, hrid, hrfrom, hrto, pts, hptsR, hpts⟩ :=
    lxe_shiftAll_routeIdx hroutes hrM
  have hrS : r ∈ s.layoutDump.routes := hrBmem
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hE r hrS
  obtain ⟨qP, hqPhead, hqPfun⟩ := lxe_mapM_point_head _ _ hpts p hp
  obtain ⟨wP, hwP, hqPeq, _⟩ := movePoint_ok hqPfun
  have hwPeq : wP = axis.point p + delta := by
    have happEq : (Move.constant delta).apply (axis.point p) =
        Measure.checkedI32 (axis.point p + delta) := by simp [Move.apply, Move.offset]
    rw [happEq] at hwP
    exact checked_value hwP
  have hqPEq : qP = axis.withPoint p (axis.point p + delta) := by rw [hqPeq, hwPeq]
  obtain ⟨qQ, hqQlast, hqQfun⟩ := lxe_mapM_point_getLast _ _ hpts q hq
  obtain ⟨wQ, hwQ, hqQeq, _⟩ := movePoint_ok hqQfun
  have hwQeq : wQ = axis.point q + delta := by
    have happEq : (Move.constant delta).apply (axis.point q) =
        Measure.checkedI32 (axis.point q + delta) := by simp [Move.apply, Move.offset]
    rw [happEq] at hwQ
    exact checked_value hwQ
  have hqQEq : qQ = axis.withPoint q (axis.point q + delta) := by rw [hqQeq, hwQeq]
  have hfb' : s.boxes.find? (fun b => b.id == r.fromId) = some fb := hfb
  have htb' : s.boxes.find? (fun b => b.id == r.toId) = some tb := htb
  obtain ⟨b0', hfindF, hidF, hrectF⟩ := lxe_shiftAll_boxIdx hboxes hnodupB hfb'
  obtain ⟨b1', hfindT, hidT, hrectT⟩ := lxe_shiftAll_boxIdx hboxes hnodupB htb'
  have hendF : endRect axis frames b0' =
      axis.withStart (endRect axis frames fb)
        (axis.start (endRect axis frames fb) + delta) :=
    lxe_endRect_shift hrectF hidF
  have hendT : endRect axis frames b1' =
      axis.withStart (endRect axis frames tb)
        (axis.start (endRect axis frames tb) + delta) :=
    lxe_endRect_shift hrectT hidT
  have hbP : Validator.onBoundary qP (endRect axis frames b0') := by
    rw [hqPEq, hendF]
    exact (onBoundary_crossShift).mpr hb1
  have hbQ : Validator.onBoundary qQ (endRect axis frames b1') := by
    rw [hqQEq, hendT]
    exact (onBoundary_crossShift).mpr hb2
  have hfindF' : (boxes.find? fun b => b.id == r'.fromId) = some b0' := by
    rw [hrfrom]; exact hfindF
  have hfindT' : (boxes.find? fun b => b.id == r'.toId) = some b1' := by
    rw [hrto]; exact hfindT
  have hhead : r'.points.head? = some qP := by rw [hptsR]; exact hqPhead
  have hlast : r'.points.getLast? = some qQ := by rw [hptsR]; exact hqQlast
  exact ⟨qP, qQ, b0', b1', hhead, hlast, hfindF', hfindT', hbP, hbQ⟩

/-- `restoreOrigin` preserves `EndsOnOld`: it either leaves the scene or shifts it. -/
private theorem lxe_phaseRestore_holds : lepePhaseRestore := by
  intro axis frames s s' h hnodupB hE
  obtain rfl | ⟨delta, _, hshift⟩ := restoreOrigin_cases h
  · exact hE
  · exact lxe_shiftAll_ends hshift hnodupB hE

/-- `relocateLabels` preserves `EndsOnOld`: boxes and routes are untouched. -/
private theorem lxe_phaseRelocate_holds : lepePhaseRelocate := by
  intro axis frames s strip hE r hr
  have hrS : r ∈ s.layoutDump.routes := hr
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hE r hrS
  exact ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩

/-- `growCanvas` preserves `EndsOnOld`: boxes and routes are untouched. -/
private theorem lxe_phaseGrow_holds : lepePhaseGrow := by
  intro axis frames canvas s s' h hE r hr
  obtain ⟨hb, hrEq, _⟩ := growCanvas_frame h
  have hdB : s'.layoutDump.boxes = s.layoutDump.boxes := hb
  have hdR : s'.layoutDump.routes = s.layoutDump.routes := hrEq
  have hrS : r ∈ s.layoutDump.routes := by rw [← hdR]; exact hr
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hE r hrS
  have hfb' : s'.layoutDump.box? r.fromId = some fb := by
    unfold LayoutDump.box?
    rw [hdB]
    exact hfb
  have htb' : s'.layoutDump.box? r.toId = some tb := by
    unfold LayoutDump.box?
    rw [hdB]
    exact htb
  exact ⟨p, q, fb, tb, hp, hq, hfb', htb', hb1, hb2⟩

/-- Shared transport tail: given ends for the routed scene of an executed
`pinBands` run, restore/relocate/grow carry them to the `pinBands` result.
Proof-only transport; the reroute phase supplies `hErouted` in the canonical
literal form. -/
theorem pinBands_ends_of_routed {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hlanes : lanesOf boxes ≠ [])
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (h : pinBands boxes o s = .ok r)
    (hErouted : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ pinned routed : Scene,
        applyPin (buildPin (Axis.ofDirection o.direction)
            (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s =
          .ok pinned →
        rerouteBands (Axis.ofDirection o.direction) sp
          (LayoutConst.rank_gap.get o.profile)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes))
          (buildPin (Axis.ofDirection o.direction)
            (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
          s.routes pinned = .ok routed →
        EndsOnOld (Axis.ofDirection o.direction)
          (laneFrames (Axis.ofDirection o.direction)
            (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
          routed.layoutDump) :
    ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        r.layoutDump := by
  obtain ⟨sp, axis, bands, pinned, routed, origin, strip, stripScene,
    hsp, haxis, hbands, happ, hroute, horig, hstrip, hstripEq, hgrow⟩ :=
    pinBands_spec hlanes h
  subst haxis
  subst hbands
  have hE := hErouted sp hsp pinned routed happ hroute
  intro sp' hsp'
  have hspEq : sp' = sp := Except.ok.inj (hsp'.symm.trans hsp)
  rw [hspEq]
  obtain ⟨shiftedBoxes, _, _, _, hboxes, _, _, _, hfold⟩ := applyPin_shifted happ
  have hid1 : shiftedBoxes.map (·.id) = s.boxes.map (·.id) :=
    (pinShiftBoxes_maps _ _ _ _ hboxes).2.1
  have hid2 : pinned.boxes.map (·.id) = shiftedBoxes.map (·.id) :=
    (foldReplaceFrame_all _ _ _ _ hfold).2.1
  have hrr : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
  have hnodupRouted : (routed.boxes.map (·.id)).Nodup := by
    rw [hrr, hid2, hid1]
    exact hnodupB
  have horigE := lxe_phaseRestore_holds horig hnodupRouted hE
  have hstripE : EndsOnOld (Axis.ofDirection o.direction)
      (laneFrames (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
      stripScene.layoutDump := by
    rw [hstripEq]
    exact lxe_phaseRelocate_holds horigE
  exact lxe_phaseGrow_holds hgrow hstripE

/-- After `pinBands`, every route end lies on its end box boundary, or on the
old frame when the end box is a lane frame: the executed-band form of
`pinBands_ends`. The two arbitrary-band premises are replaced by the
executed-band phases. The extra `hNoEmpty` premise (every scene box id is
nonempty) comes from the apply Exec form, which the universal lacks. -/
theorem pinBands_ends_exec {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC5 : Validator.C5 s.layoutDump)
    (hlanes : lanesOf boxes ≠ [])
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hEnds : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ rt ∈ s.routes,
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.fromId =
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.toId ∨
        ((Axis.ofDirection o.direction).point (rt.points.head?.getD ⟨0, 0⟩) ≠
          (Axis.ofDirection o.direction).point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (hEndsPin : FindRouteEndsPin)
    (hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (hApplyExec : lepePhaseApplyPinExec boxes o s)
    (hRerouteExec : lepePhaseRerouteExec boxes o s)
    (h : pinBands boxes o s = .ok r) :
    ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        r.layoutDump := by
  refine pinBands_ends_of_routed hlanes hnodupB h ?_
  intro sp hsp pinned routed happ hroute
  have hpin := hApplyExec sp hsp hC5 hrouteNodup hnodupB hNoEmpty hModelClean
    (hEnds sp hsp) happ
  exact hRerouteExec sp hsp hnodupB hModelClean hEndsPin happ hpin hC5 hroute

/-- Executed-band ends closed by the two narrow residuals: frame transport
gives the apply phase and fresh-ends gives the reroute phase. No premise
quantifies over arbitrary bands or scenes. -/
theorem pinBands_ends_exec_closed {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC5 : Validator.C5 s.layoutDump)
    (hlanes : lanesOf boxes ≠ [])
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hEnds : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ rt ∈ s.routes,
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.fromId =
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.toId ∨
        ((Axis.ofDirection o.direction).point (rt.points.head?.getD ⟨0, 0⟩) ≠
          (Axis.ofDirection o.direction).point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (hEndsPin : FindRouteEndsPin)
    (hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (hFrame : lppaFrameTransportResidual boxes o s)
    (hFresh : lepeRerouteFreshEndsExec boxes o s)
    (h : pinBands boxes o s = .ok r) :
    ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        r.layoutDump :=
  pinBands_ends_exec hC5 hlanes hrouteNodup hnodupB hNoEmpty hEnds hEndsPin
    hModelClean (lepePhaseApplyPinExec_holds hFrame)
    (lepePhaseRerouteExec_holds hFresh) h

end LaneBands
end Layered
end Elegant
