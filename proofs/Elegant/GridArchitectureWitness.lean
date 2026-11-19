import Elegant.GridArchitectureHierarchy

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def popCountWitnessInput : Input :=
  ⟨[0], [⟨-1,0,0,false⟩], []⟩

def popCountWitnessParams : Params := ⟨14,6,4,[]⟩

def popCountWitnessFrames : FrameParams := ⟨2,1,1,2⟩

/-- One service inside one group causes one service pop plus one root-level group pop. -/
def popCountWitness : Nat :=
  2000 - (placeHierarchy popCountWitnessInput popCountWitnessParams popCountWitnessFrames 2000).fuel

/-- The plan's real-node-count bound, with the native global pop counter. -/
def ArchPopsBoundedStatement (input : Input) (p : Params) (fp : FrameParams) (fuel : Nat) : Prop :=
  fuel - (placeHierarchy input p fp fuel).fuel ≤ input.parents.length

end Elegant.Grid.Architecture
