import Elegant.Chart.Radar

set_option autoImplicit false

namespace Elegant.Kinds.Radar

open Chart.Radar

def unzigzag (n : Int) : Int :=
  if Int.fmod n 2 = 1 then -Int.fdiv (n + 1) 2 else Int.fdiv n 2

def decodeRegion (inp : Input) (r : List Int) : Input :=
  if 7 ≤ r.length ∧ r.head? = some 0 then
    { inp with
      circle := r.getD 1 0 == 0
      showLegend := r.getD 2 0 == 1
      ticks := r.getD 3 0
      maximum := if r.getD 4 0 == 1 then some (unzigzag (r.getD 5 0)) else none
      minimum := unzigzag (r.getD 6 0) }
  else if 2 ≤ r.length ∧ r.head? = some 1 then
    { inp with curves := inp.curves ++ [{ values := ((r.drop 2).take (r.getD 1 0).toNat).map unzigzag }] }
  else inp

def decodeLabel (inp : Input) (l : ModelLabel) : Input :=
  if l.id.startsWith "legend." then
    match (String.ofList (l.id.toList.drop 7)).toNat? with
    | some i => { inp with curves := inp.curves.zipIdx.map fun (c, k) =>
        if k == i then { c with label := l.text } else c }
    | none => inp
  else if l.id.startsWith "axis." then { inp with axes := inp.axes ++ [l.text] }
  else if l.id == "title" then { inp with title := l.text }
  else inp

def decode (m : Model) : Input :=
  let inp := m.regionSets.foldl (fun acc r => decodeRegion acc r.regions) {}
  m.labels.foldl decodeLabel inp

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match Chart.Radar.layout m (decode m) with
  | .error e => .error (.geometry e)
  | .ok scene => .ok { scene, budgetExhausted := false }

end Elegant.Kinds.Radar
