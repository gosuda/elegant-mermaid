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

/-- A junction whose caption wraps past the parent frame's bottom padding: before the
junction-frame admission check the pixel-profile layout produced a dump whose junction box
escaped its parent group frame (clause C3). The guard rejects it with `geometry.domain`. -/
def c3WitnessModel : Model :=
  { kind := "architecture", profile := .vector, options := { profile := .vector }
    boxes := [ { id := "g", role := .group, exclusive := false, text := some "G" },
               { id := "j", role := .node, parent := "g", exclusive := true,
                 shape := "junction",
                 text := some (String.intercalate " " (List.replicate 20 "aaabbbbcccddddee")) } ] }

/-- The same model with a one-line junction caption: admitted and fully valid. -/
def c3WitnessControl : Model :=
  { kind := "architecture", profile := .vector, options := { profile := .vector }
    boxes := [ { id := "g", role := .group, exclusive := false, text := some "G" },
               { id := "j", role := .node, parent := "g", exclusive := true,
                 shape := "junction", text := some "j" } ] }

def c3WitnessWellFormed : Bool := modelWellFormed c3WitnessModel

def c3WitnessWithinLimits : Bool := decide (WithinLimits c3WitnessModel)

/-- The guarded adapter answers `geometry.domain` for the overflowing junction caption. -/
def c3WitnessRejected : Bool :=
  match Kinds.Architecture.layout c3WitnessModel with
  | .error (.geometry .domain) => true
  | _ => false

/-- The short-caption control is admitted and its dump passes the full validator. -/
def c3WitnessControlValid : Bool :=
  match Kinds.Architecture.layout c3WitnessControl with
  | .ok result => Validator.check result.scene.layoutDump
  | _ => false

/-- Same verdicts under the cell profile. -/
def c3WitnessCellRejected : Bool :=
  match Kinds.Architecture.layout { c3WitnessModel with profile := .cell } with
  | .error (.geometry .domain) => true
  | _ => false

def c3WitnessCellControlValid : Bool :=
  match Kinds.Architecture.layout { c3WitnessControl with profile := .cell } with
  | .ok result => Validator.check result.scene.layoutDump
  | _ => false

end Elegant.Grid.Architecture
