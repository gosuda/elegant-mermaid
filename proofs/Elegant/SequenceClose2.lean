import Elegant.SequenceClose

set_option autoImplicit false

namespace Elegant
namespace Sequence

theorem half_eq' {v : Int} (_h : 0 ≤ v) : half v = v / 2 := by
  unfold half
  exact Int.fdiv_eq_ediv_of_nonneg _ (by decide)

theorem sectionHeight_ge (c : Consts) (n : Nat) : c.boxMargin + c.boxTextMargin + (n : Int) * c.lineHeight ≤
    sectionHeight c n := Int.le_max_right _ _

theorem adv_title {pl : Plan} {f : FragRun} (hk : (f.kind == fragmentKindRect) = false) {p : Nat}
    (hp : labelPosById pl.m (boxId pl.m f.box ++ ".label") = some p) :
    adv pl f = sectionHeight pl.c (pl.labelLines.getD p []).length := by
  unfold adv fragmentAdvance
  simp only [hk, Bool.false_eq_true, ↓reduceIte]
  have : labelPosById pl.m (((pl.m.boxes[f.box]?.map (·.id)).getD "") ++ ".label") = some p := hp
  rw [this]
  rfl

theorem hgt_label {pl : Plan} {d : Divider} {p : Nat} (hp : d.label = some p) :
    hgt pl d = sectionHeight pl.c (pl.labelLines.getD p []).length := by
  unfold hgt
  rw [hp]
  rfl

theorem newLab_props {pl : Plan} (hpl : pl.Wf) {f : FragRun} {F r : Rect} {cursor : Int}
    (hk : (f.kind == fragmentKindRect) = false) (hFy : F.y = f.top)
    (hFh : F.y + F.h = cursor + pl.c.boxMargin)
    (hcov : pl.labelWidth (labelPosById pl.m (boxId pl.m f.box ++ ".label")) + 2 * pl.c.boxMargin ≤ F.w ∧
      ∀ d ∈ f.dividers, pl.labelWidth d.label + 2 * pl.c.boxMargin ≤ F.w)
    (hfa : f.top + adv pl f ≤ cursor ∧ ∀ d ∈ f.dividers, f.top + adv pl f ≤ d.row ∧ d.row + hgt pl d ≤ cursor)
    (hr : NewLab pl f F r) :
    f.top < r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ (∃ b ∈ bandsOf pl f, b.1 ≤ r.y ∧ r.y + r.h ≤ b.2) ∧
      r.y + r.h ≤ cursor ∧ F.StrictInside r := by
  have hbm := hpl.pos.boxMargin
  have hbt := hpl.pos.boxTextMargin
  have hlh := hpl.pos.lineHeight
  have hadv := fragmentAdvance_pos pl hpl f.kind f.box
  have hadv' : 0 < adv pl f := hadv
  rcases hr with ⟨p, hp, hlt, rfl⟩ | ⟨d, hd, p, hp, hlt, rfl⟩
  · have ha := adv_title hk hp
    have hsh := sectionHeight_ge pl.c (pl.labelLines.getD p []).length
    have hw := widest_nonneg (pl.labelLines.getD p [])
    have hn : 0 ≤ ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight :=
      Int.mul_nonneg (Int.natCast_nonneg _) hlh
    have hc := hcov.1
    simp only [hp, Plan.labelWidth, Plan.linesAt] at hc
    have hd0 : 0 ≤ F.w - widest (pl.labelLines.getD p []) := by omega
    have hh := half_eq' hd0
    refine ⟨?_, ?_, ?_, ⟨(f.top, f.top + adv pl f), ?_, ?_, ?_⟩, ?_, ?_⟩
    · show f.top < f.top + (pl.c.boxMargin + pl.c.boxTextMargin); omega
    · exact hw
    · exact hn
    · simp [bandsOf]
    · show f.top ≤ f.top + (pl.c.boxMargin + pl.c.boxTextMargin); omega
    · show f.top + (pl.c.boxMargin + pl.c.boxTextMargin) + ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight ≤ f.top + adv pl f
      omega
    · show f.top + (pl.c.boxMargin + pl.c.boxTextMargin) + ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight ≤ cursor
      omega
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show F.x < F.x + half (F.w - widest (pl.labelLines.getD p []))
        omega
      · show F.x + half (F.w - widest (pl.labelLines.getD p [])) + widest (pl.labelLines.getD p []) < F.x + F.w
        omega
      · show F.y < f.top + (pl.c.boxMargin + pl.c.boxTextMargin); omega
      · show f.top + (pl.c.boxMargin + pl.c.boxTextMargin) + ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight < F.y + F.h
        omega
  · have ha := hfa.2 d hd
    have hg := hgt_label (pl := pl) hp
    have hsh := sectionHeight_ge pl.c (pl.labelLines.getD p []).length
    have hw := widest_nonneg (pl.labelLines.getD p [])
    have hn : 0 ≤ ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight :=
      Int.mul_nonneg (Int.natCast_nonneg _) hlh
    have hc := hcov.2 d hd
    simp only [hp, Plan.labelWidth, Plan.linesAt] at hc
    have hd0 : 0 ≤ F.w - widest (pl.labelLines.getD p []) := by omega
    have hh := half_eq' hd0
    refine ⟨?_, ?_, ?_, ⟨(d.row, d.row + hgt pl d), ?_, ?_, ?_⟩, ?_, ?_⟩
    · show f.top < d.row + (pl.c.boxMargin + pl.c.boxTextMargin); omega
    · exact hw
    · exact hn
    · simp only [bandsOf, List.mem_cons, List.mem_map]
      exact Or.inr ⟨d, hd, rfl⟩
    · show d.row ≤ d.row + (pl.c.boxMargin + pl.c.boxTextMargin); omega
    · show d.row + (pl.c.boxMargin + pl.c.boxTextMargin) + ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight ≤ d.row + hgt pl d
      omega
    · show d.row + (pl.c.boxMargin + pl.c.boxTextMargin) + ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight ≤ cursor
      omega
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show F.x < F.x + half (F.w - widest (pl.labelLines.getD p []))
        omega
      · show F.x + half (F.w - widest (pl.labelLines.getD p [])) + widest (pl.labelLines.getD p []) < F.x + F.w
        omega
      · show F.y < d.row + (pl.c.boxMargin + pl.c.boxTextMargin); omega
      · show d.row + (pl.c.boxMargin + pl.c.boxTextMargin) + ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight < F.y + F.h
        omega

theorem strict_of_member {pl : Plan} (hpl : pl.Wf) {F r e : Rect} {span : Int × Int} {width natural cursor top : Int}
    (hFx : F.x = span.1 - pl.c.boxMargin - half (width - natural)) (hFw : F.w = width)
    (hnat : natural = span.2 - span.1 + 2 * pl.c.boxMargin) (hge : natural ≤ width)
    (hFy : F.y = top) (hFh : F.y + F.h = cursor + pl.c.boxMargin)
    (hr1 : span.1 ≤ r.x) (hr2 : r.x + r.w ≤ span.2) (hr3 : top + 1 ≤ r.y) (hr4 : r.y + r.h ≤ cursor)
    (hc : r.Contained e) : F.StrictInside e := by
  have hbm := hpl.pos.boxMargin
  have h0 : 0 ≤ half (width - natural) := half_nonneg (by omega)
  have h1 := half_le (v := width - natural) (by omega)
  unfold Rect.Contained at hc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Sequence
end Elegant
