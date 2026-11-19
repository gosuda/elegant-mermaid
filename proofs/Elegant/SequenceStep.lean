import Elegant.SequenceClose4

set_option autoImplicit false

/-! The invariant steps for a message and a note (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem half_div (v : Int) : half v = v / 2 := by
  unfold half
  exact Int.fdiv_eq_ediv_of_nonneg _ (by decide)

theorem markDestroyed_boxRects (w : Walk) (bits : Nat) (destroyed y : Int) :
    (markDestroyed w bits destroyed y).boxRects = w.boxRects := by
  unfold markDestroyed; split <;> rfl

theorem markDestroyed_labelRects (w : Walk) (bits : Nat) (destroyed y : Int) :
    (markDestroyed w bits destroyed y).labelRects = w.labelRects := by
  unfold markDestroyed; split <;> rfl

theorem placeLabel_boxRects (w : Walk) (pos : Option Nat) (r : Rect) :
    (w.placeLabel pos r).boxRects = w.boxRects := by
  unfold Walk.placeLabel; split <;> rfl

theorem placeLabel_labelRects (w : Walk) (pos : Option Nat) (r : Rect) :
    (w.placeLabel pos r).labelRects = match pos with | some p => w.labelRects.set p r | none => w.labelRects := by
  unfold Walk.placeLabel; split <;> rfl

theorem createdBox_boxRects (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).1.boxRects =
      match createdRect pl cs bits dst y with
      | some q => w.boxRects.set q.1 q.2
      | none => w.boxRects := by
  unfold createdBox
  cases createdRect pl cs bits dst y with
  | none => rfl
  | some q => simp [addMember_boxRects]

theorem createdBox_labelRects (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).1.labelRects = w.labelRects := by
  unfold createdBox
  cases createdRect pl cs bits dst y with
  | none => rfl
  | some q => simp [addMember_labelRects]

theorem createdBox_fragments (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).1.fragments =
      match createdRect pl cs bits dst y with
      | some q => fragsAdd w.fragments q.2
      | none => w.fragments := by
  unfold createdBox
  cases createdRect pl cs bits dst y with
  | none => rfl
  | some q => simp [addMember_fragments]

theorem createdBox_snd (pl : Plan) (cs : List Int) (w : Walk) (bits dst : Nat) (y : Int) :
    (createdBox pl cs w bits dst y).2 =
      match createdRect pl cs bits dst y with
      | some q => q.2.h + pl.c.boxMargin
      | none => 0 := by
  unfold createdBox
  cases createdRect pl cs bits dst y with
  | none => rfl
  | some q => rfl

def msgCount (pl : Plan) (route : Nat) : Int := ((pl.linesAt (messageLabelAt pl route)).length : Int)

def msgLw (pl : Plan) (route : Nat) : Int := widest (pl.linesAt (messageLabelAt pl route))

def msgY (pl : Plan) (w : Walk) (route : Nat) : Int :=
  w.cursor + pl.c.messageTop + msgCount pl route * pl.c.lineHeight

def msgDx (pl : Plan) (src dst route : Nat) : Int :=
  if src == dst then max (half (msgLw pl route + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx else 0

def msgRowH (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat) : Int :=
  (if src == dst then pl.c.messageTop + msgCount pl route * pl.c.lineHeight + pl.c.boxMargin + pl.c.selfLoopDepth
    else pl.c.messageTop + msgCount pl route * pl.c.lineHeight + pl.c.boxMargin) +
    (createdBox pl cs w bits dst (msgY pl w route)).2

def msgLabelRect (pl : Plan) (cs : List Int) (w : Walk) (src dst route : Nat) : Rect :=
  ⟨half (cs.getD src 0 + cs.getD dst 0) - half (msgLw pl route), w.cursor + pl.c.messageTop, msgLw pl route,
    msgCount pl route * pl.c.lineHeight⟩

def msgMember (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat) : Rect :=
  ⟨min (cs.getD src 0) (cs.getD dst 0) - msgDx pl src dst route, w.cursor,
    (max (cs.getD src 0) (cs.getD dst 0) - min (cs.getD src 0) (cs.getD dst 0)) + 2 * msgDx pl src dst route,
    msgRowH pl cs w bits src dst route⟩

theorem stepMessage_cursor_eq (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    (stepMessage pl cs w bits src dst route destroyed).cursor = w.cursor + msgRowH pl cs w bits src dst route := by
  unfold stepMessage
  simp only [Walk.advance, addMember_cursor, placeLabel_cursor, markDestroyed_cursor, createdBox_cursor]
  rfl

theorem stepMessage_boxRects_eq (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    (stepMessage pl cs w bits src dst route destroyed).boxRects =
      match createdRect pl cs bits dst (msgY pl w route) with
      | some q => w.boxRects.set q.1 q.2
      | none => w.boxRects := by
  unfold stepMessage
  simp only [Walk.advance, addMember_boxRects, placeLabel_boxRects, markDestroyed_boxRects]
  exact createdBox_boxRects pl cs w bits dst _

theorem stepMessage_labelRects_eq (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    (stepMessage pl cs w bits src dst route destroyed).labelRects =
      match messageLabelAt pl route with
      | some p => w.labelRects.set p (msgLabelRect pl cs w src dst route)
      | none => w.labelRects := by
  unfold stepMessage
  simp only [Walk.advance, addMember_labelRects, placeLabel_labelRects, markDestroyed_labelRects,
    createdBox_labelRects]
  rfl

theorem stepMessage_fragments_eq (pl : Plan) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    (stepMessage pl cs w bits src dst route destroyed).fragments =
      fragsAddAll w.fragments
        (((createdRect pl cs bits dst (msgY pl w route)).map (·.2)).toList ++
          [msgMember pl cs w bits src dst route]) := by
  unfold stepMessage
  simp only [Walk.advance, addMember_fragments, placeLabel_fragments, markDestroyed_fragments,
    createdBox_fragments]
  show fragsAdd (match createdRect pl cs bits dst (msgY pl w route) with
      | some q => fragsAdd w.fragments q.2 | none => w.fragments) (msgMember pl cs w bits src dst route) =
    fragsAddAll w.fragments (((createdRect pl cs bits dst (msgY pl w route)).map (·.2)).toList ++
      [msgMember pl cs w bits src dst route])
  cases hc : createdRect pl cs bits dst (msgY pl w route) with
  | none =>
    simp only [Option.map_none, Option.toList_none, List.nil_append]
    rw [fragsAdd_eq_all]
  | some q =>
    simp only [Option.map_some, Option.toList_some, List.singleton_append]
    have := foldl_fragsAdd [q.2, msgMember pl cs w bits src dst route] w.fragments
    simp only [List.foldl_cons, List.foldl_nil] at this
    exact this

end Sequence
end Elegant
