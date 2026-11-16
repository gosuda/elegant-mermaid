import Elegant.Kinds.Architecture

set_option autoImplicit false

namespace Elegant.Grid.Architecture

/-- An acyclic developer model whose child group precedes its parent. Native
`archBuilder.validate` rejects this order before placement. -/
def forwardParentWitnessModel : Model := {
  kind := "architecture"
  profile := .cell
  options := {profile := .cell}
  boxes := [
    {id := "child",role := .group,parent := "parent",exclusive := false,text := some ""},
    {id := "parent",role := .group,parent := "",exclusive := false,text := some ""}]
}

def forwardParentWitnessWellFormed : Bool := modelWellFormed forwardParentWitnessModel

def forwardParentWitnessCheck : Option Bool :=
  match Kinds.Architecture.build forwardParentWitnessModel with
  | .error _ => none
  | .ok (scene,_) => some (Validator.check scene.layoutDump)

end Elegant.Grid.Architecture
