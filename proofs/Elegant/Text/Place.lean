import Elegant.Measure
import Elegant.Scene
import Elegant.Text.Canvas

set_option autoImplicit false

/-! Label placement of the text back end (`spec/render-cells.md`, requirements
render-cells-38 to render-cells-48 and render-cells-89 to render-cells-91).

A label is placed line by line. The clusters of a line come from the grapheme segmentation
of `Elegant.Measure`; each is written left to right from the start column of the alignment.
A cluster is written only when every cell it needs is on the canvas and free: no arm bits,
no symbol, and no label. A cluster that cannot be written is counted, never dropped
silently. -/

namespace Elegant.Text

/-- A cell that a label may be written into: no arm bits, no symbol, and no label. -/
def Cell.isFree (v : Cell) : Bool :=
  v.mask == 0 && v.symbol == 0 && v.label == Label.empty

/-- The position is on the canvas and its cell is free. -/
def Canvas.freeAt (g : Canvas) (c r : Int) : Bool :=
  decide (g.Inside c r) && (g.cellAt c r).isFree

/-- Replace the label of one cell, and nothing else. -/
def Canvas.setLabel (g : Canvas) (c r : Int) (l : Label) : Canvas :=
  g.put c r fun v => { v with label := l }

/-- Write a cluster: its text on the first cell and, for width 2, the continuation marker
on the second cell. -/
def Canvas.writeCluster (g : Canvas) (c r : Int) (text : String) : ClusterWidth → Canvas
  | .one => g.setLabel c r (.cluster text .one)
  | .two => (g.setLabel c r (.cluster text .two)).setLabel (c + 1) r .cont

/-- Every cell that a cluster of the given width needs is on the canvas and free. -/
def Canvas.fits (g : Canvas) (c r : Int) : ClusterWidth → Bool
  | .one => g.freeAt c r
  | .two => g.freeAt c r && g.freeAt (c + 1) r

/-- The cell width of a written cluster: 1 or 2. -/
def ClusterWidth.ofNat? : Nat → Option ClusterWidth
  | 1 => some .one
  | 2 => some .two
  | _ => none

/-- Write one cluster of width `w` at `(c, r)`, or `none` when it cannot be written: its
width is not 1 or 2, or a cell it needs is off the canvas or taken. -/
def Canvas.putLabel (g : Canvas) (c r : Int) (cluster : List Char) (w : Nat) : Option Canvas :=
  match ClusterWidth.ofNat? w with
  | some cw => if g.fits c r cw then some (g.writeCluster c r (String.ofList cluster) cw) else none
  | none => none

namespace Place

/-- The first column of a line of cell width `lineW` in the box that starts at column `x`
and is `w` cells wide. -/
def lineStart (align : Align) (x w lineW : Int) : Int :=
  match align with
  | .start => x
  | .middle => x + Int.fdiv (w - lineW) 2
  | .«end» => x + w - lineW

/-- The scalars of one line: its runs joined. -/
def lineChars (runs : List TextRun) : List Char :=
  (runs.map fun run => run.text.toList).flatten

/-- The canvas, the column of the next cluster, and the number of refused clusters. -/
abbrev LineState := Canvas × Int × Nat

/-- Place one cluster on the row and advance by its cell width. -/
def placeCluster (row : Int) (st : LineState) (cl : Measure.Cluster) : LineState :=
  let w := Measure.clusterWidth cl
  match st.1.putLabel st.2.1 row cl w with
  | some g => (g, st.2.1 + (w : Int), st.2.2)
  | none => (st.1, st.2.1 + (w : Int), st.2.2 + 1)

/-- Place line `k` of a text: the canvas and the number of refused clusters. -/
def placeLine (g : Canvas) (t : SceneText) (k : Nat) (text : List Char) : Canvas × Nat :=
  let clusters := Measure.segment text
  let st := clusters.foldl (placeCluster (t.rect.y + (k : Int)))
    (g, lineStart t.align t.rect.x t.rect.w ((Measure.cw clusters : Nat) : Int), 0)
  (st.1, st.2.2)

/-- Place the lines of a text from line index `k`, adding the refused clusters to `n`. -/
def placeLines (t : SceneText) : Nat → List (List TextRun) → Canvas → Nat → Canvas × Nat
  | _, [], g, n => (g, n)
  | k, runs :: rest, g, n =>
    let p := placeLine g t k (lineChars runs)
    placeLines t (k + 1) rest p.1 (n + p.2)

/-- Place every line of one text. -/
def placeText (g : Canvas) (t : SceneText) : Canvas × Nat :=
  placeLines t 0 t.lines g 0

/-- The canvas after the texts are placed in declaration order. -/
def placeCanvas (g : Canvas) (ts : List SceneText) : Canvas :=
  ts.foldl (fun acc t => (placeText acc t).1) g

/-- The number of clusters refused while the texts are placed in declaration order. -/
def refusedCount : Canvas → List SceneText → Nat
  | _, [] => 0
  | g, t :: ts => (placeText g t).2 + refusedCount (placeText g t).1 ts

/-- Place the texts in declaration order; the result is the canvas and the number of
clusters that could not be written. -/
def placeAll (g : Canvas) (ts : List SceneText) : Canvas × Nat :=
  (placeCanvas g ts, refusedCount g ts)

end Place

/-- A canvas `g'` that follows `g` by label writes only: arm bits, style, dots, and symbols are
kept, an occupied label is kept, and a label appears only in a cell that was on the canvas and
free of arm bits and symbols. -/
def Canvas.Placing (g g' : Canvas) : Prop :=
  g'.W = g.W ∧ g'.H = g.H ∧
    ∀ c r, (g'.cellAt c r).mask = (g.cellAt c r).mask ∧
      (g'.cellAt c r).style = (g.cellAt c r).style ∧
      (g'.cellAt c r).dots = (g.cellAt c r).dots ∧
      (g'.cellAt c r).symbol = (g.cellAt c r).symbol ∧
      ((g.cellAt c r).label ≠ Label.empty → (g'.cellAt c r).label = (g.cellAt c r).label) ∧
      ((g.cellAt c r).label = Label.empty → (g'.cellAt c r).label ≠ Label.empty →
        g.Inside c r ∧ (g.cellAt c r).mask = 0 ∧ (g.cellAt c r).symbol = 0)

theorem placing_refl (g : Canvas) : g.Placing g :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun he hne => absurd he hne⟩⟩

theorem placing_trans {g g' g'' : Canvas} (h : g.Placing g') (h' : g'.Placing g'') :
    g.Placing g'' := by
  obtain ⟨hw, hh, hc⟩ := h
  obtain ⟨hw', hh', hc'⟩ := h'
  refine ⟨by omega, by omega, fun c r => ?_⟩
  obtain ⟨m1, s1, d1, y1, k1, n1⟩ := hc c r
  obtain ⟨m2, s2, d2, y2, k2, n2⟩ := hc' c r
  refine ⟨by rw [m2, m1], by rw [s2, s1], by rw [d2, d1], by rw [y2, y1], fun hne => ?_,
    fun he hne => ?_⟩
  · rw [k2 (by rw [k1 hne]; exact hne), k1 hne]
  · by_cases e : (g'.cellAt c r).label = Label.empty
    · obtain ⟨hi, hm, hs⟩ := n2 e hne
      exact ⟨by unfold Canvas.Inside at hi ⊢; omega, by rw [← m1]; exact hm, by rw [← y1]; exact hs⟩
    · exact n1 he e

theorem Canvas.Placing.confined {g g' : Canvas} (h : g.Placing g') : g.Confined g' := by
  obtain ⟨hw, hh, hc⟩ := h
  refine ⟨hw, hh, fun c r hne => ?_⟩
  obtain ⟨m, s, d, y, k, n⟩ := hc c r
  by_cases e : (g.cellAt c r).label = Label.empty
  · by_cases e' : (g'.cellAt c r).label = Label.empty
    · exfalso
      apply hne
      cases hg : g'.cellAt c r
      cases hg0 : g.cellAt c r
      simp only [hg, hg0] at m s d y e e'
      simp_all
    · exact (n e e').1
  · exfalso
    apply hne
    cases hg : g'.cellAt c r
    cases hg0 : g.cellAt c r
    have := k e
    simp only [hg, hg0] at m s d y this
    simp_all

theorem freeAt_iff (g : Canvas) (c r : Int) :
    g.freeAt c r = true ↔
      g.Inside c r ∧ (g.cellAt c r).mask = 0 ∧ (g.cellAt c r).symbol = 0 ∧
        (g.cellAt c r).label = Label.empty := by
  simp [Canvas.freeAt, Cell.isFree, Bool.and_eq_true, and_assoc]

theorem setLabel_cellAt (g : Canvas) (c r : Int) (l : Label) (c' r' : Int) :
    (g.setLabel c r l).cellAt c' r' =
      if g.Inside c r ∧ c' = c ∧ r' = r then { g.cellAt c r with label := l }
      else g.cellAt c' r' := by
  unfold Canvas.setLabel
  rw [cellAt_put]

theorem setLabel_inside_iff (g : Canvas) (c r : Int) (l : Label) (c' r' : Int) :
    (g.setLabel c r l).Inside c' r' ↔ g.Inside c' r' :=
  put_inside_iff g c r _ c' r'

theorem freeAt_setLabel_ne (g : Canvas) (c r : Int) (l : Label) (c' r' : Int)
    (h : ¬(c' = c ∧ r' = r)) : (g.setLabel c r l).freeAt c' r' = g.freeAt c' r' := by
  have hn : ¬(g.Inside c r ∧ c' = c ∧ r' = r) := fun hh => h hh.2
  have hi := setLabel_inside_iff g c r l c' r'
  unfold Canvas.freeAt
  rw [setLabel_cellAt]
  simp only [hn, ↓reduceIte]
  exact congrArg (· && _) (decide_eq_of_iff hi)

theorem setLabel_cellAt_hit (g : Canvas) {c r : Int} (l : Label) (h : g.Inside c r) :
    (g.setLabel c r l).cellAt c r = { g.cellAt c r with label := l } := by
  rw [setLabel_cellAt]
  simp [h]

theorem setLabel_cellAt_miss (g : Canvas) (c r : Int) (l : Label) {c' r' : Int}
    (h : ¬(c' = c ∧ r' = r)) : (g.setLabel c r l).cellAt c' r' = g.cellAt c' r' := by
  rw [setLabel_cellAt]
  have hn : ¬(g.Inside c r ∧ c' = c ∧ r' = r) := fun hh => h hh.2
  simp only [hn, ↓reduceIte]

theorem placing_setLabel {g : Canvas} {c r : Int} (l : Label) (h : g.freeAt c r = true) :
    g.Placing (g.setLabel c r l) := by
  obtain ⟨hin, hm, hs, he⟩ := (freeAt_iff g c r).mp h
  refine ⟨put_W g c r _, put_H g c r _, fun c' r' => ?_⟩
  by_cases e : c' = c ∧ r' = r
  · obtain ⟨hc, hr⟩ := e
    subst hc hr
    rw [setLabel_cellAt_hit g l hin]
    exact ⟨rfl, rfl, rfl, rfl, fun hne => absurd he hne, fun _ _ => ⟨hin, hm, hs⟩⟩
  · rw [setLabel_cellAt_miss g c r l e]
    exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun he' hne => absurd he' hne⟩

theorem putLabel_placing {g g' : Canvas} {c r : Int} {cl : List Char} {w : Nat}
    (h : g.putLabel c r cl w = some g') : g.Placing g' := by
  unfold Canvas.putLabel at h
  cases hw : ClusterWidth.ofNat? w with
  | none => simp [hw] at h
  | some cw =>
    simp only [hw] at h
    split at h
    · rename_i hf
      simp only [Option.some.injEq] at h
      subst h
      cases cw with
      | one =>
        exact placing_setLabel _ hf
      | two =>
        simp only [Canvas.fits, Bool.and_eq_true] at hf
        unfold Canvas.writeCluster
        refine placing_trans (placing_setLabel _ hf.1) (placing_setLabel _ ?_)
        have hne : ¬(c + 1 = c ∧ r = r) := fun hh => by omega
        rw [freeAt_setLabel_ne g c r _ (c + 1) r hne]
        exact hf.2
    · simp at h

namespace Place

theorem placeCluster_placing (row : Int) (st : LineState) (cl : Measure.Cluster) :
    st.1.Placing (placeCluster row st cl).1 := by
  unfold placeCluster
  dsimp only
  split
  · rename_i g h
    exact putLabel_placing h
  · exact placing_refl _

theorem foldl_placeCluster_placing (row : Int) :
    ∀ (cs : List Measure.Cluster) (st : LineState),
      st.1.Placing (cs.foldl (placeCluster row) st).1 := by
  intro cs
  induction cs with
  | nil => intro st; exact placing_refl _
  | cons cl cs ih =>
    intro st
    exact placing_trans (placeCluster_placing row st cl) (ih (placeCluster row st cl))

theorem placeLine_placing (g : Canvas) (t : SceneText) (k : Nat) (text : List Char) :
    g.Placing (placeLine g t k text).1 :=
  foldl_placeCluster_placing (t.rect.y + (k : Int)) (Measure.segment text) _

theorem placeLines_placing (t : SceneText) :
    ∀ (ls : List (List TextRun)) (k : Nat) (g : Canvas) (n : Nat),
      g.Placing (placeLines t k ls g n).1 := by
  intro ls
  induction ls with
  | nil => intro k g n; exact placing_refl _
  | cons runs rest ih =>
    intro k g n
    exact placing_trans (placeLine_placing g t k (lineChars runs)) (ih (k + 1) _ _)

theorem placeText_placing (g : Canvas) (t : SceneText) : g.Placing (placeText g t).1 :=
  placeLines_placing t t.lines 0 g 0

theorem placeCanvas_placing (ts : List SceneText) :
    ∀ g : Canvas, g.Placing (placeCanvas g ts) := by
  induction ts with
  | nil => intro g; exact placing_refl _
  | cons t ts ih =>
    intro g
    exact placing_trans (placeText_placing g t) (ih (placeText g t).1)

/-- A line that fits its box starts and ends inside the box, for every alignment. -/
theorem lineStart_inside_rect (align : Align) (x w lineW : Int) (_h0 : 0 ≤ lineW)
    (h1 : lineW ≤ w) :
    x ≤ lineStart align x w lineW ∧ lineStart align x w lineW + lineW ≤ x + w := by
  cases align <;> simp only [lineStart]
  · omega
  · rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  · omega

/-- A cell that holds label text after `placeAll` had no arm bits and no symbol before, and
`placeAll` leaves every arm mask and every symbol unchanged. The canvas that `placeAll`
receives holds no label text, because placement runs after lines, dots, and symbols. -/
theorem label_never_overwrites_border (g : Canvas) (ts : List SceneText)
    (hg : ∀ c r, (g.cellAt c r).label = Label.empty) (c r : Int) :
    (((placeAll g ts).1.cellAt c r).label ≠ Label.empty →
        (g.cellAt c r).mask = 0 ∧ (g.cellAt c r).symbol = 0) ∧
      ((placeAll g ts).1.cellAt c r).mask = (g.cellAt c r).mask ∧
      ((placeAll g ts).1.cellAt c r).symbol = (g.cellAt c r).symbol := by
  obtain ⟨_, _, hc⟩ := placeCanvas_placing ts g
  obtain ⟨m, _, _, y, _, n⟩ := hc c r
  exact ⟨fun hne => (n (hg c r) hne).2, m, y⟩

/-- The general form of the border rule: a label that appears in a cell that held none was
written into a free cell. -/
theorem label_written_only_into_free (g : Canvas) (ts : List SceneText) (c r : Int)
    (h0 : (g.cellAt c r).label = Label.empty)
    (h1 : ((placeAll g ts).1.cellAt c r).label ≠ Label.empty) :
    g.Inside c r ∧ (g.cellAt c r).mask = 0 ∧ (g.cellAt c r).symbol = 0 := by
  obtain ⟨_, _, hc⟩ := placeCanvas_placing ts g
  exact (hc c r).2.2.2.2.2 h0 h1

/-- Item `i` of the list puts label text into the cell `(c, r)`: the cell holds none after
the items before `i` are placed, and holds some after item `i` is placed too. -/
def Placed (g : Canvas) (ts : List SceneText) (i : Nat) (c r : Int) : Prop :=
  ((placeCanvas g (ts.take i)).cellAt c r).label = Label.empty ∧
    ((placeCanvas g (ts.take (i + 1))).cellAt c r).label ≠ Label.empty

theorem take_succ_placing (g : Canvas) (ts : List SceneText) (n : Nat) :
    (placeCanvas g (ts.take n)).Placing (placeCanvas g (ts.take (n + 1))) := by
  rw [List.take_add_one]
  unfold placeCanvas
  rw [List.foldl_append]
  cases ts[n]? with
  | none => exact placing_refl _
  | some t => exact placeText_placing _ t

theorem take_label_const (g : Canvas) (ts : List SceneText) (c r : Int) (n : Nat)
    (h : ((placeCanvas g (ts.take n)).cellAt c r).label ≠ Label.empty) :
    ∀ k, ((placeCanvas g (ts.take (n + k))).cellAt c r).label =
      ((placeCanvas g (ts.take n)).cellAt c r).label := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨_, _, hc⟩ := take_succ_placing g ts (n + k)
    rw [← Nat.add_assoc, (hc c r).2.2.2.2.1 (by rw [ih]; exact h), ih]

theorem placed_exists (g : Canvas) (ts : List SceneText)
    (hg : ∀ c r, (g.cellAt c r).label = Label.empty) (c r : Int) :
    ∀ m, ((placeCanvas g (ts.take m)).cellAt c r).label ≠ Label.empty →
      ∃ i, i < m ∧ Placed g ts i c r := by
  intro m
  induction m with
  | zero =>
    intro h
    exact absurd (hg c r) h
  | succ m ih =>
    intro h
    by_cases hm : ((placeCanvas g (ts.take m)).cellAt c r).label = Label.empty
    · exact ⟨m, Nat.lt_succ_self m, hm, h⟩
    · obtain ⟨i, hi, hp⟩ := ih hm
      exact ⟨i, Nat.lt_succ_of_lt hi, hp⟩

/-- After `placeAll`, no cell holds text from two different labels: every cell that holds
label text received it from exactly one item of the list, and keeps what that item wrote.
The canvas that `placeAll` receives holds no label text. -/
theorem place_labels_disjoint (g : Canvas) (ts : List SceneText)
    (hg : ∀ c r, (g.cellAt c r).label = Label.empty) (c r : Int)
    (h : ((placeAll g ts).1.cellAt c r).label ≠ Label.empty) :
    ∃ i, i < ts.length ∧ Placed g ts i c r ∧ (∀ j, Placed g ts j c r → j = i) ∧
      ((placeAll g ts).1.cellAt c r).label =
        ((placeCanvas g (ts.take (i + 1))).cellAt c r).label := by
  have hfull : placeCanvas g (ts.take ts.length) = (placeAll g ts).1 := by
    rw [List.take_length]
    rfl
  have hP : ((placeCanvas g (ts.take ts.length)).cellAt c r).label ≠ Label.empty := by
    rw [hfull]
    exact h
  obtain ⟨i, hi, hpl⟩ := placed_exists g ts hg c r ts.length hP
  refine ⟨i, hi, hpl, fun j hj => ?_, ?_⟩
  · refine Classical.byContradiction fun hne => ?_
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := take_label_const g ts c r (j + 1) hj.2 (i - (j + 1))
      rw [Nat.add_sub_cancel' (by omega)] at this
      exact hj.2 (this.symm.trans hpl.1)
    · have := take_label_const g ts c r (i + 1) hpl.2 (j - (i + 1))
      rw [Nat.add_sub_cancel' (by omega)] at this
      exact hpl.2 (this.symm.trans hj.1)
  · have := take_label_const g ts c r (i + 1) hpl.2 (ts.length - (i + 1))
    rw [Nat.add_sub_cancel' (by omega), hfull] at this
    exact this

end Place

end Elegant.Text
