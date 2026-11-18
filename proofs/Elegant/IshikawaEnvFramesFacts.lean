import Elegant.IshikawaClearanceHardA
import Elegant.IshikawaClearanceHardBFinal

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- The ENV side condition of HARD B holds for every executed rib:
`IshikawaEnvFrames` unfolds to `IshikawaEnvInvariant`, which
`ishikawa_env_invariant` proves from a successful `layout` and `place`. -/
theorem ishikawa_env_frames (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hcause : cause ∈ children ns 0)
    (hrib : generatedRib ns (cause, k) ∈ ribs)
    (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) :
    IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) :=
  ishikawa_env_invariant ns p raw hrun ribs hg cause k hcause hrib spine placed hplace

end Elegant.Ishikawa
