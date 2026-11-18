import Elegant.Layered.ExpandChildContainment
import Elegant.Model

set_option autoImplicit false

/-!
# The recursion context of an `expandChild` call `layoutRecursive` performs

`ExpandChildCallContext` packages the facts the per-expansion step discharges
(`ExpandChildC2Step`, `ExpandChildC6Step`, `ExpandChildC7Step`,
`ExpandChildC8aStep`, `ExpandChildC8bStep`) need that hold only for the calls
the recursion actually makes: well-formedness of the splitting input, the
`find?` witness that selects `group`, the two recursive results, and the
parent sub-input `selectInput` shape `hpboxes` pins.  The recursive lifts
state their `hgeo` hypothesis over this context so that each `succ` case
passes exactly what `layoutRecursive_succ_sources` /
`layoutRecursive_embedding_assembly_sources` expose.

Premises some steps need beyond this package — nonempty box ids (`hids`,
which `modelWellFormed` does not check) and `framedParents` — stay separate
`hgeo` binders on the lifts that consume them.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound


/-- The child sub-input `layoutRecursive` builds for `group`: the boxes
inside the group, rooted at the group. -/
def childSubInput (inp : Input) (group : ModelBox) : Input :=
  selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id

/-- The child sub-options `layoutRecursive` builds: the group's direction. -/
def childSubOptions (o : Options) (group : ModelBox) : Options :=
  { o with direction := directionOf group.direction }

/-- The parent sub-input `layoutRecursive` builds for `group`: the boxes
outside the group, carrying the measured group frame as fixed data (the
exact construction `layoutRecursive` performs and
`layoutRecursive_embedding_assembly_sources` pins). -/
def parentSubInput (inp : Input) (group : ModelBox) (P : Params)
    (titleLines : List Measure.Line) (child : FamilyResult) : Input :=
  { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
    fixedSizes :=
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedSizes ++
        [(group.id, childFrameSize group.direction P.clusterPad
            (titleLines.foldl (fun width line => max width line.width) 0)
            ((max 1 titleLines.length : Int) * P.lineH)
            ⟨child.scene.canvas.w - 2 * P.canvasMargin,
              child.scene.canvas.h - 2 * P.canvasMargin⟩)]
    fixedChildren :=
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedChildren ++
        [(group.id, child.scene)]
    fixedAreas :=
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)).fixedAreas ++
        [(group.id, child.itemArea)] }
/-- The context an `expandChild` call inside `layoutRecursive` runs under at
the given fuel: the input `inp` is well-formed, `group` is the box the
recursion's `find?` selects, `hchild` and `hparent` are the two recursive
successes at the actual `childSubInput`/`parentSubInput` the recursion
builds (whose `.boxes` are the `selectInput` lists, the fixed side tables
`layoutRecursive` appends notwithstanding).  `titleLines` is the wrapped
group title the parent frame size is measured from. -/
def ExpandChildCallContext (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult) : Prop :=
  WellFormed (inputModel inp o) ∧
    inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
    (parentSubInput inp group P titleLines child).boxes =
      (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes ∧
    layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child ∧
    layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent ∧
    expandChild P inp o group titleHeight parent child = .ok res

end Elegant.Layered.PipelineImpl
