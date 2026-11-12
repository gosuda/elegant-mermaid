import ElegantGeometry.Compaction
import ElegantGeometry.Crossings
import ElegantGeometry.Route
import ElegantGeometry.Trig

set_option autoImplicit false

namespace ElegantGeometry.Eval

def integer (s : String) : Option Int := do
  let n ← s.toInt?
  if toString n == s && decide (InI32 n) then some n else none

def inner (left right : Char) (s : String) : Option String :=
  match s.toList with
  | [] => none
  | c :: cs => if c == left && cs.getLast? == some right then
      some (String.ofList (cs.take (cs.length - 1))) else none

def tuple (s : String) : Option (List Int) := do
  let body ← inner '(' ')' s
  let ns ← (body.splitOn ",").mapM integer
  if ns.length == 2 || ns.length == 4 then some ns else none

def splitItems : List Char → Nat → List Char → List String → List String
  | [], _, acc, out => (String.ofList acc.reverse :: out).reverse
  | c :: cs, depth, acc, out =>
    if c == ',' && depth == 0 then splitItems cs depth [] (String.ofList acc.reverse :: out)
    else splitItems cs (if c == '(' then depth + 1 else if c == ')' then depth - 1 else depth) (c :: acc) out

def items (s : String) : Option (List String) := do
  let body ← inner '[' ']' s
  if body.isEmpty then some [] else some (splitItems body.toList 0 [] [])

def rect (s : String) : Option Rect := do
  match ← tuple s with
  | [x,y,w,h] => some ⟨x,y,w,h⟩
  | _ => none

def point (s : String) : Option Point := do
  match ← tuple s with
  | [x,y] => some ⟨x,y⟩
  | _ => none

def size (s : String) : Option Size := do
  let p ← point s
  some ⟨p.x,p.y⟩

def segment (s : String) : Option Segment := do
  match ← tuple s with
  | [a,b,c,d] => some ⟨⟨a,b⟩,⟨c,d⟩⟩
  | _ => none

def axis : String → Option Axis
  | "X" => some .X
  | "Y" => some .Y
  | _ => none

def validResult (s : String) : Bool :=
  if ["true","false","overflow","domain"].contains s then true
  else if (integer s).isSome || (tuple s).isSome then true
  else match items s with
    | none => false
    | some xs => xs.all (fun x => (integer x).isSome || (tuple x).isSome)

def rectToken (r : Rect) : String := s!"({r.x},{r.y},{r.w},{r.h})"

def token {α : Type} (f : α → String) : Except LayoutError α → String
  | .ok x => f x
  | .error .domain => "domain"
  | .error .overflow => "overflow"

def boolToken (b : Bool) : String := if b then "true" else "false"

def rectsToken (rs : List Rect) : String := "[" ++ String.intercalate "," (rs.map rectToken) ++ "]"

abbrev bounded (x : Int) : Prop := -COORD_LIMIT ≤ x ∧ x ≤ COORD_LIMIT

def hits (ps : List Point) (r : Rect) : Except LayoutError Bool :=
  if r.Valid ∧ bounded r.x ∧ bounded r.y ∧ bounded (r.x+r.w) ∧ bounded (r.y+r.h) ∧
      ∀ p ∈ ps, bounded p.x ∧ bounded p.y then
    match ps with
    | [p] => .ok (decide (0 < r.w ∧ 0 < r.h) && !(Polyline.segMissesB p p r))
    | _ => .ok (Polyline.hitsRectB ps r)
  else .error .domain

def evaluate : List String → Option String
  | ["translate",r,x,y] => do
      return token rectToken ((← rect r).translate (← integer x) (← integer y))
  | ["inflate",r,d] => do return token rectToken ((← rect r).inflate (← integer d))
  | ["union",a,b] => do return token rectToken ((← rect a).union (← rect b))
  | ["intersects",a,b] => do return token boolToken ((← rect a).intersects (← rect b))
  | ["contains",a,b] => do return token boolToken ((← rect a).contains (← rect b))
  | ["place_after",a,r,g,s] => do
      return token rectToken (Rect.placeAfter (← axis a) (← rect r) (← integer g) (← size s))
  | ["compact",a,g,rs] => do
      return token rectsToken (compact (← axis a) (← integer g) (← (← items rs).mapM rect))
  | ["segments_cross",s,t] => do return token boolToken ((← segment s).cross (← segment t))
  | ["is_orthogonal",ps] => do return boolToken (Polyline.isOrthogonal (← (← items ps).mapM point))
  | ["polyline_hits_rect",ps,r] => do return token boolToken (hits (← (← items ps).mapM point) (← rect r))
  | ["count_inversions",xs] => do return token toString (countInversions (← (← items xs).mapM integer))
  | ["isqrt",n] => do return token toString (Rect.isqrt (← integer n))
  | ["sin_q15",n] => do return toString (sinQ15 (← integer n))
  | ["cos_q15",n] => do return toString (cosQ15 (← integer n))
  | _ => none

def evalLine (line : String) : Except Unit String :=
  let fields := line.splitOn " "
  match fields.reverse with
  | result :: "->" :: rest =>
      if validResult result then
        match evaluate rest.reverse with
        | some s => .ok s
        | none => .error ()
      else .error ()
  | _ => .error ()

def runLines : List String → Nat → String → Except Nat String
  | [], _, out => .ok out
  | [""], _, out => .ok out
  | [_], n, _ => .error n
  | line :: rest, n, out =>
    match evalLine line with
    | .error _ => .error n
    | .ok s => runLines rest (n+1) (out ++ s ++ "\n")

def run (text : String) : Except Nat String := runLines (text.splitOn "\n") 1 ""

end ElegantGeometry.Eval
