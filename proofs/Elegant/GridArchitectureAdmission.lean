import Elegant.GridArchitectureGeometry

set_option autoImplicit false

namespace Elegant.Grid.Architecture

/-- Native `archBuilder.validate`, kept separate from executable dispatch until
malformed developer-model witnesses have been executed by the integration owner. -/
def nativeAdmission (p : GeometryParams) (fp : FrameParams) (fuel ringCap : Int)
    (nodes : List Node) (groups : List Group) (edges : List Edge)
    (edgeLabels : List Size) (aligns : List Alignment) : Bool :=
  decide (0 < p.pitchX ∧ 0 < p.pitchY ∧ 0 < p.iconW ∧ 0 < p.iconH ∧
    0 ≤ fp.padding ∧ 0 ≤ p.lineHeight ∧ 0 ≤ p.badge ∧ 0 ≤ p.inset ∧
    0 ≤ p.labelGap ∧ 0 ≤ p.thickness ∧ 0 ≤ fuel ∧ 0 ≤ ringCap ∧
    (p.gutter = 0 ∨ p.gutter = 1)) &&
  groups.zipIdx.all (fun q => decide (-1 ≤ q.1.parent ∧ q.1.parent < Int.ofNat q.2 ∧
    0 ≤ q.1.titleW ∧ 0 ≤ q.1.titleH)) &&
  nodes.all (fun n => decide (-1 ≤ n.parent ∧ n.parent < Int.ofNat groups.length ∧
    0 < n.icon.w ∧ 0 < n.icon.h ∧ 0 ≤ n.label.w ∧ 0 ≤ n.label.h)) &&
  edges.all (fun e => decide (e.a < nodes.length ∧ e.b < nodes.length)) &&
  edgeLabels.all (fun s => decide (0 ≤ s.w ∧ 0 ≤ s.h)) &&
  aligns.all (fun a => a.members.all (fun n => decide (n < nodes.length)))

end Elegant.Grid.Architecture
