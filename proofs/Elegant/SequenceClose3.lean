import Elegant.SequenceClose2

set_option autoImplicit false

namespace Elegant
namespace Sequence

theorem fragsAdd_eq_all (fs : List FragRun) (r : Rect) : fragsAdd fs r = fragsAddAll fs [r] := by
  have := foldl_fragsAdd [r] fs
  simpa using this

theorem mem_fragsAdd {fs : List FragRun} {r : Rect} {g : FragRun} (h : g ∈ fragsAdd fs r) :
    ∃ g0 ∈ fs, g.top = g0.top ∧ g.kind = g0.kind ∧ g.box = g0.box ∧ g.dividers = g0.dividers ∧
      (∀ x ∈ g.members, x ∈ g0.members ∨ x = r) ∧ (∀ x ∈ g0.members, x ∈ g.members) := by
  rw [fragsAdd_eq_all] at h
  obtain ⟨g0, hg0, h1, h2, h3, h4, h5, h6⟩ := mem_fragsAddAll h
  exact ⟨g0, hg0, h1, h2, h3, h4, fun x hx => (h5 x hx).imp id (fun h => by simpa using h), h6⟩

theorem fragsAdd_map_box (fs : List FragRun) (r : Rect) :
    (fragsAdd fs r).map (·.box) = fs.map (·.box) := by
  cases fs <;> simp [fragsAdd]

theorem chainS_top_of {m : Model} (hfm : ModelFacts m) {stk : List Nat} (hc : ChainOK m stk)
    (hlt : ∀ s ∈ stk, s < m.boxes.length) (hlen : stk.length ≤ m.boxes.length) :
    ∀ g ∈ stk, ChainS m (topId m stk) (boxId m g) := by
  cases stk with
  | nil => intro g hg; simp at hg
  | cons s0 rest => exact chainS_stack m hfm.nodup hfm.nonempty s0 rest hc hlt hlen

theorem boxId_ne_topId {m : Model} (hfm : ModelFacts m) {stk : List Nat}
    (hlt : ∀ s ∈ stk, s < m.boxes.length) {g : Nat} (hg : g < m.boxes.length) (hgs : g ∉ stk) :
    boxId m g ≠ topId m stk := by
  cases stk with
  | nil => exact hfm.nonempty g hg
  | cons s0 rest =>
    intro h
    have := boxId_inj hfm hg (hlt s0 List.mem_cons_self) h
    exact hgs (by rw [this]; exact List.mem_cons_self)

theorem topId_host_of {m : Model} {stk placed : List Nat} (hs : ∀ s ∈ stk, s ∈ placed) :
    topId m stk = "" ∨ ∃ t ∈ placed, topId m stk = boxId m t := by
  cases stk with
  | nil => exact Or.inl rfl
  | cons s0 rest => exact Or.inr ⟨s0, hs s0 List.mem_cons_self, rfl⟩

theorem closeWith_labelRects (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (closeWith pl w run width).labelRects =
      if run.kind == fragmentKindRect then w.labelRects
      else run.dividers.foldl (fun ls d => centreLabel pl ls d.label (frameRect pl w run width)
          (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)))
        (centreLabel pl w.labelRects (labelPosById pl.m (boxId pl.m run.box ++ ".label"))
          (frameRect pl w run width) (run.top + (pl.c.boxMargin + pl.c.boxTextMargin))) := by
  unfold closeWith
  rw [addMember_labelRects]
  rfl

theorem closeLabels_length (pl : Plan) (ls : List Rect) (f : FragRun) (F : Rect) :
    (f.dividers.foldl (fun ls d => centreLabel pl ls d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)))
      (centreLabel pl ls (labelPosById pl.m (boxId pl.m f.box ++ ".label")) F
        (f.top + (pl.c.boxMargin + pl.c.boxTextMargin)))).length = ls.length := by
  have key : ∀ (ds : List Divider) (l0 : List Rect),
      (ds.foldl (fun ls d => centreLabel pl ls d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin))) l0).length
        = l0.length := by
    intro ds
    induction ds with
    | nil => intro l0; rfl
    | cons d t ih =>
      intro l0
      simp only [List.foldl_cons]
      rw [ih, centreLabel_length]
  rw [key, centreLabel_length]

def labelEntRects (pl : Plan) (f : FragRun) (F : Rect) : List Rect :=
  (match labelPosById pl.m (boxId pl.m f.box ++ ".label") with
    | some p =>
      if p < pl.labelLines.length then
        [centredRect pl p F (f.top + (pl.c.boxMargin + pl.c.boxTextMargin))]
      else []
    | none => []) ++
  f.dividers.flatMap fun d =>
    match d.label with
    | some p =>
      if p < pl.labelLines.length then
        [centredRect pl p F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin))]
      else []
    | none => []

theorem mem_labelEntRects {pl : Plan} {f : FragRun} {F r : Rect} :
    r ∈ labelEntRects pl f F ↔ NewLab pl f F r := by
  unfold labelEntRects NewLab
  constructor
  · intro hr
    rcases List.mem_append.mp hr with h | h
    · left
      cases ht : labelPosById pl.m (boxId pl.m f.box ++ ".label") with
      | none => simp [ht] at h
      | some p =>
        by_cases hp : p < pl.labelLines.length
        · simp only [ht, hp, ↓reduceIte, List.mem_singleton] at h
          exact ⟨p, rfl, hp, h⟩
        · simp [ht, hp] at h
    · right
      obtain ⟨d, hd, h'⟩ := List.mem_flatMap.mp h
      cases hdl : d.label with
      | none => simp [hdl] at h'
      | some p =>
        by_cases hp : p < pl.labelLines.length
        · simp only [hdl, hp, ↓reduceIte, List.mem_singleton] at h'
          exact ⟨d, hd, p, hdl, hp, h'⟩
        · simp [hdl, hp] at h'
  · intro hr
    rcases hr with ⟨p, hp, hlt, rfl⟩ | ⟨d, hd, p, hp, hlt, rfl⟩
    · apply List.mem_append_left
      simp [hp, hlt]
    · apply List.mem_append_right
      refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
      simp [hp, hlt]

end Sequence
end Elegant
