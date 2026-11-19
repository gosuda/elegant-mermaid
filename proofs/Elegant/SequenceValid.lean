import Elegant.SequenceValid8

set_option autoImplicit false

namespace Elegant
namespace Sequence

/-- Successful sequence layouts satisfy all eight hard constraints. Inconsistent developer
model dumps are rejected at the sequence input boundary, before the geometry walk. -/
theorem sequence_valid {model : Model} (hwf : WellFormed model) (_hlim : WithinLimits model)
    {s : Scene} (h : layout model = .ok s) :
    HardConstraints s.layoutDump := by
  have hk := layout_admissible h
  obtain ⟨pl, steps, cs, w, ck, E, F, hd⟩ := final_facts hwf hk h
  rw [hd]
  exact ⟨dump_c1 F, dump_c2 F, dump_c3 F, dump_c4 F, dump_c5 F, dump_c6 F, dump_c7 F, dump_c8 F⟩

end Sequence
end Elegant
