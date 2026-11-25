import Elegant.Layered.LaneEndsClauses
import Elegant.LanesEventmodelingTidyFacts

set_option autoImplicit false

/-! Route-clause transport for the final lane-end attachment (design items 5-8).

`attachLaneEnds` slides a route end along the cross axis when it sat on the old
frame side, keeping the rank coordinate, then simplifies. This preserves
orthogonality (C4), lands moved ends on the stretched frame boundary (C5), and
keeps clearance (C6) because the new gap segment runs through the strip between
the old and the new frame side, which `GapClear` keeps free of exclusive boxes. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Binding step of an `Except` computation (local copy; the clauses file keeps its own private copy). -/
private theorem lerc_bindOk {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A rank-preserving move is axis-aligned. -/
private theorem lerc_aligned_of_rank {axis : Axis} {p q : Point}
    (h : axis.other.point q = axis.other.point p) : Elegant.Grid.Aligned p q := by
  cases axis with
  | x =>
    simp only [Axis.other, Axis.point] at h
    unfold Elegant.Grid.Aligned
    exact Or.inr h.symm
  | y =>
    simp only [Axis.other, Axis.point] at h
    unfold Elegant.Grid.Aligned
    exact Or.inl h.symm

/-- An aligned miss is an axis miss (wraps the lanes proof). -/
private theorem lerc_axMiss_of_segMisses_aligned {a b : Point} {box : Rect}
    (ha : Elegant.Grid.Aligned a b) (hm : Polyline.segMisses a b box) :
    Elegant.Grid.AxMiss box a b :=
  Elegant.Lanes.Eventmodeling.aligned_segMisses_axis ha hm

/-- An orthogonal, missing polyline is an axis-miss chain. -/
private theorem lerc_chain_axmiss_of {o : Rect} : ∀ (ps : List Point),
    Elegant.Grid.Chain Elegant.Grid.Aligned ps → Polyline.allSegsMiss ps o →
    Elegant.Grid.Chain (Elegant.Grid.AxMiss o) ps
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | p :: q :: rest, hAl, hMiss => by
    simp only [Polyline.allSegsMiss] at hMiss
    exact ⟨lerc_axMiss_of_segMisses_aligned hAl.1 hMiss.1,
      lerc_chain_axmiss_of (q :: rest) hAl.2 hMiss.2⟩

/-- A moved end keeps the rank coordinate (wraps the clauses-file fact). -/
private theorem lerc_rank_of_move {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {id : String} {p q : Point}
    (h : attachEnd axis frames boxes id p = .ok (some q)) :
    axis.other.point q = axis.other.point p :=
  attachEnd_rank h

/-- The raw (unsimplified) attachment of one route is aligned when the old route is. -/
private theorem lerc_raw_aligned {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {r : Route} {first last : Point} {ho to_ : Option Point}
    (hhead : r.points.head? = some first) (hlast : r.points.getLast? = some last)
    (hAl : Elegant.Grid.Chain Elegant.Grid.Aligned r.points)
    (e1 : attachEnd axis frames boxes r.fromId first = .ok ho)
    (e2 : attachEnd axis frames boxes r.toId last = .ok to_) :
    Elegant.Grid.Chain Elegant.Grid.Aligned (ho.toList ++ r.points ++ to_.toList) := by
  cases hpts : r.points with
  | nil => simp only [hpts] at hhead; cases hhead
  | cons f rest =>
    have hhead' : (f :: rest).head? = some first := hpts ▸ hhead
    have hf : f = first := Option.some.inj (by simpa using hhead')
    have hlast' : (f :: rest).getLast? = some last := hpts ▸ hlast
    have hAl' : Elegant.Grid.Chain Elegant.Grid.Aligned (f :: rest) := hpts ▸ hAl
    cases ho with
    | none =>
      cases to_ with
      | none =>
        simp only [Option.toList_none, List.nil_append, List.append_nil]
        exact hAl'
      | some t' =>
        simp only [Option.toList_none, Option.toList_some, List.nil_append, List.cons_append]
        have hA : Elegant.Grid.Aligned last t' :=
          lerc_aligned_of_rank (lerc_rank_of_move e2)
        exact Elegant.Grid.chain_snoc hAl' hlast' hA
    | some h' =>
      cases to_ with
      | none =>
        simp only [Option.toList_none, Option.toList_some, List.nil_append, List.append_nil, List.cons_append]
        have hA : Elegant.Grid.Aligned h' f := by
          have hr := lerc_rank_of_move e1
          rw [← hf] at hr
          exact lerc_aligned_of_rank hr.symm
        exact ⟨hA, hAl'⟩
      | some t' =>
        simp only [Option.toList_some, List.nil_append, List.cons_append]
        have hA : Elegant.Grid.Aligned h' f := by
          have hr := lerc_rank_of_move e1
          rw [← hf] at hr
          exact lerc_aligned_of_rank hr.symm
        have hB : Elegant.Grid.Aligned last t' :=
          lerc_aligned_of_rank (lerc_rank_of_move e2)
        have hPre : Elegant.Grid.Chain Elegant.Grid.Aligned (h' :: f :: rest) :=
          ⟨hA, hAl'⟩
        have hlastPre : (h' :: f :: rest).getLast? = some last := by
          simpa using hlast'
        exact Elegant.Grid.chain_snoc hPre hlastPre hB


/-- Item 5: orthogonality survives the final attachment. -/
theorem attachLaneEnds_c4 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC4 : Validator.C4 s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C4 d'.layoutDump := by
  intro r' hr' horth
  obtain ⟨r, hmem, _hid, _hfrom, _hto, horthEq, hshape⟩ := attachLaneEnds_mem h hr'
  have hr : r ∈ s.layoutDump.routes := hmem
  have hC4r := hC4 r hr (by rw [← horthEq]; exact horth)
  rcases hshape with hpts | ⟨first, last, ho, to_, hhead, hlast, e1, e2, hreq⟩
  · rw [hpts]
    exact hC4r
  · have hEq : r'.points = simplifyPoints (ho.toList ++ r.points ++ to_.toList) := hreq
    rw [hEq]
    have hChain : Elegant.Grid.Chain Elegant.Grid.Aligned
        (ho.toList ++ r.points ++ to_.toList) :=
      lerc_raw_aligned hhead hlast (chain_aligned_of_orthogonal r.points hC4r) e1 e2
    exact simplifyPoints_orthogonal hChain

/-- Item 6: a moved end lands on the stretched frame boundary. -/
theorem attachEnd_boundary {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {id : String} {p : Point} {b : Box} {o : Option Point}
    (hb : boxes.find? (fun b => b.id == id) = some b)
    (hfit : ∀ f : LaneFrame, frames.find? (fun b => b.id == id) = some f →
      0 ≤ f.near ∧ f.near + f.length ≤ axis.length b.rect)
    (hbound : Validator.onBoundary p (endRect axis frames b))
    (h : attachEnd axis frames boxes id p = .ok o) :
    Validator.onBoundary (o.getD p) b.rect := by
  unfold attachEnd at h
  cases hf : frames.find? (fun b => b.id == id) with
  | none =>
    have hpred := (List.find?_eq_some_iff_append.mp hb).1
    have hbid : b.id = id := beq_iff_eq.mp (by simpa using hpred)
    subst hbid
    simp only [hf] at h
    have hok : Except.ok (none : Option Point) = Except.ok o := h
    cases hok
    simp only [Option.getD_none]
    unfold endRect at hbound
    simp only [hf] at hbound
    exact hbound
  | some f =>
    cases hb2 : boxes.find? (fun b => b.id == id) with
    | none =>
      have hcontra : (some b : Option Box) = none := by rw [← hb, hb2]
      cases hcontra
    | some b2 =>
      have hpred := (List.find?_eq_some_iff_append.mp hb).1
      have hbid : b.id = id := beq_iff_eq.mp (by simpa using hpred)
      subst hbid
      have _hbeq : b2 = b := Option.some.inj (by rw [← hb2, hb])
      have hfit' := hfit f hf
      unfold endRect at hbound
      simp only [hf] at hbound
      simp only [hf, hb] at h
      by_cases hhi : axis.point p = axis.start b.rect + f.near + f.length
      · simp only [hhi, ↓reduceIte] at h
        obtain ⟨v, hv, ho⟩ := lerc_bindOk h
        have hvEq : v = axis.start b.rect + axis.length b.rect :=
          Elegant.Measure.checkedI32_ok hv
        have hoEq : (some (axis.withPoint p v) : Option Point) = o := Except.ok.inj ho
        have hget : o.getD p = axis.withPoint p v := by rw [← hoEq]; rfl
        rw [hget, hvEq]
        unfold Validator.onBoundary at hbound ⊢
        cases axis with
        | x =>
          simp only [oldFrame, placeRect, Axis.start, Axis.length, Axis.withStart,
            Axis.withLength, Axis.withPoint] at hbound ⊢
          obtain ⟨hx1, hx2, hy1, hy2, _hside⟩ := hbound
          obtain ⟨hfit1, hfit2⟩ := hfit'
          simp only [Axis.length] at hfit1 hfit2
          refine ⟨by omega, by omega, hy1, hy2, by simp⟩
        | y =>
          simp only [oldFrame, placeRect, Axis.start, Axis.length, Axis.withStart,
            Axis.withLength, Axis.withPoint] at hbound ⊢
          obtain ⟨hx1, hx2, hy1, hy2, _hside⟩ := hbound
          obtain ⟨hfit1, hfit2⟩ := hfit'
          simp only [Axis.length] at hfit1 hfit2
          refine ⟨hx1, hx2, by omega, by omega, by simp⟩
      · simp only [hhi, ↓reduceIte] at h
        by_cases hlo : axis.point p = axis.start b.rect + f.near
        · simp only [hlo, ↓reduceIte] at h
          have hoEq : (some (axis.withPoint p (axis.start b.rect)) : Option Point) = o :=
            Except.ok.inj h
          have hget : o.getD p = axis.withPoint p (axis.start b.rect) := by
            rw [← hoEq]; rfl
          rw [hget]
          unfold Validator.onBoundary at hbound ⊢
          cases axis with
          | x =>
            simp only [oldFrame, placeRect, Axis.start, Axis.withStart,
              Axis.withLength, Axis.withPoint] at hbound ⊢
            obtain ⟨hx1, hx2, hy1, hy2, _hside⟩ := hbound
            obtain ⟨hfit1, hfit2⟩ := hfit'
            simp only [Axis.start, Axis.length] at hfit1 hfit2 hlo
            refine ⟨by omega, by omega, hy1, hy2, by simp⟩
          | y =>
            simp only [oldFrame, placeRect, Axis.start, Axis.withStart,
              Axis.withLength, Axis.withPoint] at hbound ⊢
            obtain ⟨hx1, hx2, hy1, hy2, _hside⟩ := hbound
            obtain ⟨hfit1, hfit2⟩ := hfit'
            simp only [Axis.start, Axis.length] at hfit1 hfit2 hlo
            refine ⟨hx1, hx2, by omega, by omega, by simp⟩
        · simp only [hlo, ↓reduceIte] at h
          have hoEq : (none : Option Point) = o := Except.ok.inj h
          have hget : o.getD p = p := by rw [← hoEq]; rfl
          rw [hget]
          unfold Validator.onBoundary at hbound ⊢
          cases axis with
          | x =>
            simp only [oldFrame, placeRect, Axis.start, Axis.withStart,
              Axis.withLength] at hbound ⊢
            obtain ⟨hx1, hx2, hy1, hy2, hside⟩ := hbound
            obtain ⟨hfit1, hfit2⟩ := hfit'
            simp only [Axis.start, Axis.length, Axis.point] at hhi hlo hfit1 hfit2
            refine ⟨by omega, by omega, hy1, hy2, ?_⟩
            rcases hside with h | h | h | h
            · exact False.elim (hlo h)
            · exact False.elim (hhi h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
          | y =>
            simp only [oldFrame, placeRect, Axis.start, Axis.withStart,
              Axis.withLength] at hbound ⊢
            obtain ⟨hx1, hx2, hy1, hy2, hside⟩ := hbound
            obtain ⟨hfit1, hfit2⟩ := hfit'
            simp only [Axis.start, Axis.length, Axis.point] at hhi hlo hfit1 hfit2
            refine ⟨hx1, hx2, by omega, by omega, ?_⟩
            rcases hside with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact False.elim (hlo h)
            · exact False.elim (hhi h)

/-- The raw attachment starts at the moved head (or the old head). -/
private theorem lerc_raw_head {r : Route} {first : Point} {ho to_ : Option Point}
    (hhead : r.points.head? = some first) :
    (ho.toList ++ r.points ++ to_.toList).head? = some (ho.getD first) := by
  cases ho with
  | none =>
    cases hr : r.points with
    | nil => simp [hr] at hhead
    | cons f rest =>
      have hf : f = first := Option.some.inj (by simpa [hr] using hhead)
      subst hf
      simp
  | some h' =>
    cases hr : r.points with
    | nil => simp [hr] at hhead
    | cons f rest =>
      simp

/-- The raw attachment ends at the moved tail (or the old tail). -/
private theorem lerc_raw_last {r : Route} {last : Point} {ho to_ : Option Point}
    (hlast : r.points.getLast? = some last) :
    (ho.toList ++ r.points ++ to_.toList).getLast? = some (to_.getD last) := by
  cases to_ with
  | none =>
    cases ho with
    | none =>
      simp only [Option.toList_none, List.nil_append, List.append_nil, Option.getD_none]
      exact hlast
    | some h' =>
      cases hr : r.points with
      | nil => simp [hr] at hlast
      | cons f rest =>
        simp only [Option.toList_some, Option.toList_none, List.append_nil, Option.getD_none]
        have hlast' : (f :: rest).getLast? = some last := hr ▸ hlast
        have hEq : ([h'] ++ (f :: rest)).getLast? = (f :: rest).getLast? := by simp
        rw [hEq, hlast']
  | some t' =>
    simp only [Option.toList_some, Option.getD_some]
    simp

/-- Item 7: C5 holds after the step, from old-frame ends and fit. -/
theorem attachLaneEnds_c5 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hEnds : EndsOnOld axis frames s.layoutDump)
    (hFit : FramesFit axis frames s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C5 d'.layoutDump := by
  unfold attachLaneEnds at h
  obtain ⟨routes, hm, hd'⟩ := lerc_bindOk h
  dsimp only at hd'
  cases hd'
  have hspec := mapM_except_spec (attachRoute axis frames s.boxes) s.routes routes hm
  intro r' hr'
  have hr'mem : r' ∈ routes := hr'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr'mem
  have hkR : k < routes.length := (List.getElem?_eq_some_iff.mp hk).1
  have hlen : routes.length = s.routes.length := hspec.1
  have hi : k < s.routes.length := by rw [← hlen]; exact hkR
  obtain ⟨a, b, ha, hb, hab⟩ := hspec.2 k hi hkR
  have hbb : (some b) = (some r') := by rw [← hb]; exact hk
  have hbeq : b = r' := Option.some.inj hbb
  subst hbeq
  have hmem : a ∈ s.routes := List.mem_of_getElem? ha
  have hmemD : a ∈ s.layoutDump.routes := hmem
  obtain ⟨p, q, fb, tb, hphead, hplast, hfb, htb, hbF, hbT⟩ := hEnds a hmemD
  obtain ⟨hid, hfrom, hto, _horth⟩ := attachRoute_ids hab
  have hfbBox : s.boxes.find? (fun b => b.id == a.fromId) = some fb := hfb
  have htbBox : s.boxes.find? (fun b => b.id == a.toId) = some tb := htb
  have hfitOf' : ∀ f : LaneFrame, frames.find? (fun b => b.id == a.fromId) = some f →
      0 ≤ f.near ∧ f.near + f.length ≤ axis.length fb.rect := by
    intro f hf
    have hfmem : f ∈ frames := List.mem_of_find?_eq_some hf
    have hpred := (List.find?_eq_some_iff_append.mp hf).1
    have hfid : f.id = a.fromId := beq_iff_eq.mp (by simpa using hpred)
    have hboxf : s.layoutDump.box? f.id = some fb := by rw [hfid]; exact hfb
    exact hFit f hfmem fb hboxf
  have hfitOt : ∀ f : LaneFrame, frames.find? (fun b => b.id == a.toId) = some f →
      0 ≤ f.near ∧ f.near + f.length ≤ axis.length tb.rect := by
    intro f hf
    have hfmem : f ∈ frames := List.mem_of_find?_eq_some hf
    have hpred := (List.find?_eq_some_iff_append.mp hf).1
    have hfid : f.id = a.toId := beq_iff_eq.mp (by simpa using hpred)
    have hboxf : s.layoutDump.box? f.id = some tb := by rw [hfid]; exact htb
    have hfitf := hFit f hfmem tb hboxf
    obtain ⟨h1, h2⟩ := hfitf
    exact ⟨h1, h2⟩
  unfold attachRoute at hab
  cases hhead : a.points.head? with
  | none =>
    simp [hhead] at hphead
  | some first =>
    cases hlast : a.points.getLast? with
    | none =>
      cases hr : a.points with
      | nil => simp [hr] at hhead
      | cons f rest =>
        simp [hr] at hlast
    | some last =>
      have hpFirst : p = first := Option.some.inj (by rw [← hphead, hhead])
      have hqLast : q = last := Option.some.inj (by rw [← hplast, hlast])
      have hbF1 : Validator.onBoundary first (endRect axis frames fb) := hpFirst ▸ hbF
      have hbT1 : Validator.onBoundary last (endRect axis frames tb) := hqLast ▸ hbT
      simp only [hhead, hlast] at hab
      obtain ⟨ho, e1, hab2⟩ := lerc_bindOk hab
      obtain ⟨to_, e2, hab3⟩ := lerc_bindOk hab2
      by_cases hboth : ho.isNone && to_.isNone
      · have hho : ho = none := by
          cases ho with
          | none => rfl
          | some _ => simp at hboth
        have hto : to_ = none := by
          cases to_ with
          | none => rfl
          | some _ => simp at hboth
        subst hho; subst hto
        have hab3' : (pure a : Except LayoutError Route) = .ok b := by simpa using hab3
        have hr'eq : a = b := Except.ok.inj hab3'
        have hptsA : b.points = a.points := by rw [← hr'eq]
        have hheadB : b.points.head? = some first := by rw [hptsA]; exact hhead
        have hlastB : b.points.getLast? = some last := by rw [hptsA]; exact hlast
        have hbFB := attachEnd_boundary hfbBox hfitOf' hbF1 e1
        have hbTB := attachEnd_boundary htbBox hfitOt hbT1 e2
        refine ⟨first, last, fb, tb, hheadB, hlastB, ?_, ?_, hbFB, hbTB⟩
        · rw [hfrom]; exact hfb
        · rw [hto]; exact htb
      · simp only [hboth] at hab3
        have hr'eq : { a with points := simplifyPoints (ho.toList ++ a.points ++ to_.toList) } = b := Except.ok.inj hab3
        have hpts : b.points = simplifyPoints (ho.toList ++ a.points ++ to_.toList) := by
          rw [← hr'eq]
        have hrawH := lerc_raw_head (ho := ho) (to_ := to_) hhead
        have hrawL := lerc_raw_last (ho := ho) (to_ := to_) hlast
        have hend := simplifyPoints_endpoints (ho.toList ++ a.points ++ to_.toList)
        have hhead' : b.points.head? = some (ho.getD first) := by
          rw [hpts, hend.1, hrawH]
        have hlast' : b.points.getLast? = some (to_.getD last) := by
          rw [hpts, hend.2, hrawL]

        have hbF2 := attachEnd_boundary hfbBox hfitOf' hbF1 e1
        have hbT2 := attachEnd_boundary htbBox hfitOt hbT1 e2
        refine ⟨ho.getD first, to_.getD last, fb, tb, hhead', hlast', ?_, ?_, hbF2, hbT2⟩
        · rw [hfrom]; exact hfb
        · rw [hto]; exact htb
/-- The new gap segment misses by cross-axis separation. -/
private theorem lerc_gap_axmiss {axis : Axis} {fbRect bRect : Rect} {near length : Int}
    {p q : Point}
    (hfit1 : 0 ≤ near) (hfit2 : near + length ≤ axis.length fbRect)
    (hlen : 0 ≤ length)
    (hgap : (axis.start fbRect + near ≤ axis.start bRect ∧
        axis.start bRect + axis.length bRect ≤ axis.start fbRect + near + length) ∨
      axis.start bRect + axis.length bRect ≤ axis.start fbRect ∨
      axis.start fbRect + axis.length fbRect ≤ axis.start bRect)
    (hseg : (axis.point p = axis.start fbRect + axis.length fbRect ∧
        axis.point q = axis.start fbRect + near + length) ∨
      (axis.point p = axis.start fbRect ∧
        axis.point q = axis.start fbRect + near)) :
    Elegant.Grid.AxMiss bRect p q := by
  unfold Elegant.Grid.AxMiss
  cases axis with
  | x =>
    simp only [Axis.start, Axis.length, Axis.point] at hfit2 hgap hseg
    omega
  | y =>
    simp only [Axis.start, Axis.length, Axis.point] at hfit2 hgap hseg
    omega

/-- A moved end forms a gap miss against an out-of-scope exclusive box. -/
private theorem lerc_move_axmiss {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {id : String} {p q : Point} {fb b : Box} {f : LaneFrame}
    (hfind : frames.find? (fun x => x.id == id) = some f)
    (hfb : boxes.find? (fun x => x.id == id) = some fb)
    (hmove : attachEnd axis frames boxes id p = .ok (some q))
    (hfit1 : 0 ≤ f.near) (hfit2 : f.near + f.length ≤ axis.length fb.rect)
    (hlen : 0 ≤ f.length)
    (hgap : (axis.start fb.rect + f.near ≤ axis.start b.rect ∧
        axis.start b.rect + axis.length b.rect ≤ axis.start fb.rect + f.near + f.length) ∨
      axis.start b.rect + axis.length b.rect ≤ axis.start fb.rect ∨
      axis.start fb.rect + axis.length fb.rect ≤ axis.start b.rect) :
    Elegant.Grid.AxMiss b.rect q p := by
  unfold attachEnd at hmove
  simp only [hfind, hfb] at hmove
  by_cases hhi : axis.point p = axis.start fb.rect + f.near + f.length
  · simp only [hhi, ↓reduceIte] at hmove
    obtain ⟨v, hv, ho⟩ := lerc_bindOk hmove
    have hvEq : v = axis.start fb.rect + axis.length fb.rect :=
      Elegant.Measure.checkedI32_ok hv
    have hoEq : (some (axis.withPoint p v) : Option Point) = some q := Except.ok.inj ho
    have hqp : q = axis.withPoint p v := (Option.some.inj hoEq).symm
    have hqcross : axis.point q = axis.start fb.rect + axis.length fb.rect := by
      rw [hqp, hvEq]
      cases axis <;> rfl
    exact lerc_gap_axmiss hfit1 hfit2 hlen hgap (Or.inl ⟨hqcross, hhi⟩)
  · simp only [hhi, ↓reduceIte] at hmove
    by_cases hlo : axis.point p = axis.start fb.rect + f.near
    · simp only [hlo, ↓reduceIte] at hmove
      have hoEq : (some (axis.withPoint p (axis.start fb.rect)) : Option Point) = some q :=
        Except.ok.inj hmove
      have hqp : q = axis.withPoint p (axis.start fb.rect) := (Option.some.inj hoEq).symm
      have hqcross : axis.point q = axis.start fb.rect := by
        rw [hqp]
        cases axis <;> rfl
      exact lerc_gap_axmiss hfit1 hfit2 hlen hgap (Or.inr ⟨hqcross, hlo⟩)
    · simp only [hlo, ↓reduceIte] at hmove
      have hok : Except.ok (none : Option Point) = Except.ok (some q) := hmove
      cases hok

/-- The raw attachment is an axis-miss chain when the old route is and gaps miss. -/
private theorem lerc_raw_axmiss {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {r : Route} {first last : Point} {ho to_ : Option Point} {o : Rect}
    (hhead : r.points.head? = some first) (hlast : r.points.getLast? = some last)
    (hOld : Elegant.Grid.Chain (Elegant.Grid.AxMiss o) r.points)
    (e1 : attachEnd axis frames boxes r.fromId first = .ok ho)
    (e2 : attachEnd axis frames boxes r.toId last = .ok to_)
    (hF : ∀ h' : Point, ho = some h' → Elegant.Grid.AxMiss o h' first)
    (hT : ∀ t' : Point, to_ = some t' → Elegant.Grid.AxMiss o last t') :
    Elegant.Grid.Chain (Elegant.Grid.AxMiss o) (ho.toList ++ r.points ++ to_.toList) := by
  cases hpts : r.points with
  | nil => simp only [hpts] at hhead; cases hhead
  | cons f rest =>
    have hhead' : (f :: rest).head? = some first := hpts ▸ hhead
    have hf : f = first := Option.some.inj (by simpa using hhead')
    have hlast' : (f :: rest).getLast? = some last := hpts ▸ hlast
    have hOld' : Elegant.Grid.Chain (Elegant.Grid.AxMiss o) (f :: rest) := hpts ▸ hOld
    cases ho with
    | none =>
      cases to_ with
      | none =>
        simp only [Option.toList_none, List.nil_append, List.append_nil]
        exact hOld'
      | some t' =>
        simp only [Option.toList_none, List.nil_append, Option.toList_some]
        have hA := hT t' rfl
        exact Elegant.Grid.chain_snoc hOld' hlast' hA
    | some h' =>
      cases to_ with
      | none =>
        simp only [Option.toList_some, Option.toList_none, List.nil_append, List.append_nil, List.cons_append]
        have hA : Elegant.Grid.AxMiss o h' f := by
          have hr := hF h' rfl
          rw [← hf] at hr
          exact hr
        exact ⟨hA, hOld'⟩
      | some t' =>
        simp only [Option.toList_some]
        have hA : Elegant.Grid.AxMiss o h' f := by
          have hr := hF h' rfl
          rw [← hf] at hr
          exact hr
        have hB := hT t' rfl
        have hPre : Elegant.Grid.Chain (Elegant.Grid.AxMiss o) (h' :: f :: rest) :=
          ⟨hA, hOld'⟩
        have hlastPre : (h' :: f :: rest).getLast? = some last := by
          simpa using hlast'
        exact Elegant.Grid.chain_snoc hPre hlastPre hB

/-- Item 8: clearance survives the step. The new gap segment runs through the
    strip between the old and the new frame side, which `GapClear` keeps free.
    Needs `FramesFit` (the old range inside the stretched range) and
    non-negative frame lengths for the strip ordering. -/
theorem attachLaneEnds_c6 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC6 : Validator.C6 s.layoutDump)
    (hOrtho : ∀ r ∈ s.layoutDump.routes, Polyline.isOrthogonal r.points = true)
    (hGap : GapClear axis frames s.layoutDump)
    (hPos : ExclusivePositive s.layoutDump)
    (hFit : FramesFit axis frames s.layoutDump)
    (hLen : ∀ f ∈ frames, 0 ≤ f.length)
    (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C6 d'.layoutDump := by
  have h0 := h
  have hfrB : d'.boxes = s.boxes := (attachLaneEnds_frame h0).1
  have hscopeEq : ∀ r1 r2 : Route, r1.fromId = r2.fromId → r1.toId = r2.toId →
      d'.layoutDump.routeScope r1 = s.layoutDump.routeScope r2 := by
    intro r1 r2 hf ht
    have hanc : ∀ id, d'.layoutDump.ancestors id = s.layoutDump.ancestors id :=
      fun id => ancestors_eq_of_frame h0 id
    unfold LayoutDump.routeScope
    rw [hf, ht]
    simp only [hanc]
  unfold attachLaneEnds at h
  obtain ⟨routes, hm, hd'⟩ := lerc_bindOk h
  dsimp only at hd'
  cases hd'
  have hspec := mapM_except_spec (attachRoute axis frames s.boxes) s.routes routes hm
  intro r' hr' c hc hex hscopeC
  have hcS : c ∈ s.boxes := hfrB ▸ hc
  have hmemS : c ∈ s.layoutDump.boxes := hcS
  have hnohit : ∀ ps : List Point, Polyline.allSegsMiss ps c.rect →
      ¬ Polyline.hitsRect ps c.rect := by
    intro ps hall hh'
    obtain ⟨_, _, nall⟩ := hh'
    exact nall hall
  have hr'mem : r' ∈ routes := hr'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr'mem
  have hkR : k < routes.length := (List.getElem?_eq_some_iff.mp hk).1
  have hlen : routes.length = s.routes.length := hspec.1
  have hi : k < s.routes.length := by rw [← hlen]; exact hkR
  obtain ⟨a, b, ha, hb, hab⟩ := hspec.2 k hi hkR
  have hbeq : b = r' := Option.some.inj (by rw [← hb]; exact hk)
  subst hbeq
  have hmem : a ∈ s.routes := List.mem_of_getElem? ha
  have hmemD : a ∈ s.layoutDump.routes := hmem
  obtain ⟨hid, hfrom, hto, _horth⟩ := attachRoute_ids hab
  have hscopeA : c.id ∉ s.layoutDump.routeScope a := by
    have hs := hscopeEq b a hfrom hto
    rw [hs] at hscopeC
    exact hscopeC
  have hpos := hPos c hmemS hex
  obtain ⟨hw, hh⟩ := hpos
  have hhit := hC6 a hmemD c hmemS hex hscopeA
  have hallOld : Polyline.allSegsMiss a.points c.rect :=
    Classical.byContradiction (fun hn => hhit ⟨hw, hh, hn⟩)
  have hAlOld := chain_aligned_of_orthogonal a.points (hOrtho a hmemD)
  have hAxOld := lerc_chain_axmiss_of a.points hAlOld hallOld
  unfold attachRoute at hab
  cases hhead : a.points.head? with
  | none =>
    cases hr : a.points with
    | nil =>
      simp only [hr] at hab
      have hab' : (pure a : Except LayoutError Route) = .ok b := by simpa using hab
      have hr'eq : a = b := Except.ok.inj hab'
      have hptsA : b.points = a.points := by rw [← hr'eq]
      have hallB : Polyline.allSegsMiss b.points c.rect := by rw [hptsA]; exact hallOld
      exact hnohit b.points hallB
    | cons f rest =>
      simp [hr] at hhead
  | some first =>
    cases hlast : a.points.getLast? with
    | none =>
      cases hr : a.points with
      | nil => simp [hr] at hhead
      | cons f rest =>
        simp [hr] at hlast
    | some last =>
      simp only [hhead, hlast] at hab
      obtain ⟨ho, e1, hab2⟩ := lerc_bindOk hab
      obtain ⟨to_, e2, hab3⟩ := lerc_bindOk hab2
      have hF : ∀ h' : Point, ho = some h' → Elegant.Grid.AxMiss c.rect h' first := by
        intro h' hheq
        have e1' : attachEnd axis frames s.boxes a.fromId first = .ok (some h') := hheq ▸ e1
        unfold attachEnd at e1'
        cases hfindF : frames.find? (fun x => x.id == a.fromId) with
        | none =>
          simp only [hfindF] at e1'
          have hok : Except.ok (none : Option Point) = Except.ok (some h') := e1'
          cases hok
        | some f =>
          cases hfbF : s.boxes.find? (fun x => x.id == a.fromId) with
          | none =>
            simp only [hfindF, hfbF] at e1'
            have hok : Except.ok (none : Option Point) = Except.ok (some h') := e1'
            cases hok
          | some fb =>
            have hfmem : f ∈ frames := List.mem_of_find?_eq_some hfindF
            have hpred := (List.find?_eq_some_iff_append.mp hfindF).1
            have hfid : f.id = a.fromId := beq_iff_eq.mp (by simpa using hpred)
            have hboxf : s.layoutDump.box? f.id = some fb := by rw [hfid]; exact hfbF
            have hfit := hFit f hfmem fb hboxf
            obtain ⟨hfit1, hfit2⟩ := hfit
            have hlen0 := hLen f hfmem
            have hne : c.id ≠ f.id := by
              intro he
              have hmemSc : c.id ∈ s.layoutDump.routeScope a := by
                rw [he, hfid]
                unfold LayoutDump.routeScope
                simp
              exact hscopeA hmemSc
            have hgap := hGap f hfmem fb hboxf c hmemS hex hne
            exact lerc_move_axmiss hfindF hfbF e1' hfit1 hfit2 hlen0 hgap
      have hT : ∀ t' : Point, to_ = some t' → Elegant.Grid.AxMiss c.rect last t' := by
        intro t' hteq
        have e2' : attachEnd axis frames s.boxes a.toId last = .ok (some t') := hteq ▸ e2
        unfold attachEnd at e2'
        cases hfindT : frames.find? (fun x => x.id == a.toId) with
        | none =>
          simp only [hfindT] at e2'
          have hok : Except.ok (none : Option Point) = Except.ok (some t') := e2'
          cases hok
        | some fT =>
          cases hfbT : s.boxes.find? (fun x => x.id == a.toId) with
          | none =>
            simp only [hfindT, hfbT] at e2'
            have hok : Except.ok (none : Option Point) = Except.ok (some t') := e2'
            cases hok
          | some fbT =>
            have hfmemT : fT ∈ frames := List.mem_of_find?_eq_some hfindT
            have hpredT := (List.find?_eq_some_iff_append.mp hfindT).1
            have hfidT : fT.id = a.toId := beq_iff_eq.mp (by simpa using hpredT)
            have hboxfT : s.layoutDump.box? fT.id = some fbT := by rw [hfidT]; exact hfbT
            have hfitT := hFit fT hfmemT fbT hboxfT
            obtain ⟨hfit1T, hfit2T⟩ := hfitT
            have hlenT := hLen fT hfmemT
            have hneT : c.id ≠ fT.id := by
              intro heT
              have hmemScT : c.id ∈ s.layoutDump.routeScope a := by
                rw [heT, hfidT]
                unfold LayoutDump.routeScope
                simp
              exact hscopeA hmemScT
            have hgapT := hGap fT hfmemT fbT hboxfT c hmemS hex hneT
            exact (lerc_move_axmiss hfindT hfbT e2' hfit1T hfit2T hlenT hgapT).symm
      by_cases hboth : ho.isNone && to_.isNone
      · have hho : ho = none := by
          cases ho with
          | none => rfl
          | some _ => simp at hboth
        have hto : to_ = none := by
          cases to_ with
          | none => rfl
          | some _ => simp at hboth
        subst hho; subst hto
        have hab3' : (pure a : Except LayoutError Route) = .ok b := by simpa using hab3
        have hr'eq : a = b := Except.ok.inj hab3'
        have hptsA : b.points = a.points := by rw [← hr'eq]
        have hallB : Polyline.allSegsMiss b.points c.rect := by rw [hptsA]; exact hallOld
        exact hnohit b.points hallB
      · simp only [hboth] at hab3
        have hr'eq : { a with points := simplifyPoints (ho.toList ++ a.points ++ to_.toList) } = b := Except.ok.inj hab3
        have hpts : b.points = simplifyPoints (ho.toList ++ a.points ++ to_.toList) := by
          rw [← hr'eq]
        have hAxRaw := lerc_raw_axmiss hhead hlast hAxOld e1 e2 hF hT
        have hAxGrid : Elegant.Grid.Chain (Elegant.Grid.AxMiss c.rect)
            (Elegant.Grid.simplify (ho.toList ++ a.points ++ to_.toList)) :=
          Elegant.Grid.simplify_misses hw hh hAxRaw
        have hAxSimp : Elegant.Grid.Chain (Elegant.Grid.AxMiss c.rect)
            (simplifyPoints (ho.toList ++ a.points ++ to_.toList)) := by
          rw [simplifyPoints_eq_grid_simplify]
          exact hAxGrid
        have hallNew := Elegant.Grid.Chain.misses hAxSimp
        have hallB : Polyline.allSegsMiss b.points c.rect := by rw [hpts]; exact hallNew
        exact hnohit b.points hallB

end LaneBands
end Layered
end Elegant
