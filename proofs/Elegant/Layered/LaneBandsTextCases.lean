import Elegant.Layered.LaneBands

set_option autoImplicit false

namespace Elegant.Layered.LaneBands

private def centeredText : SceneText :=
  { rect := ⟨10, 5, 20, 1⟩
    role := .label
    size := 14
    align := .middle
    style := "text"
    lines := [[⟨"A", false, false⟩]] }

private def textScene : Scene :=
  { kind := "swimlane", profile := .cell, options := { profile := .cell }
    canvas := ⟨50, 15⟩
    items := [⟨.node, "A", [.text centeredText]⟩] }

-- Centering reserves the actual glyph span, leaving the ordinary side port clear.
#guard (textObstacles .x textScene).map
  (fun o => (o.cross0, o.cross1, o.rank0, o.rank1)) == [(18, 21, 4, 7)]
#guard (textObstacles .x textScene).all fun o => !o.hits ⟨30, 5⟩ ⟨31, 5⟩

private def stubEnds : RouteEnds :=
  ⟨⟨29, 5⟩, ⟨40, 5⟩, ⟨5, 31⟩, ⟨5, 38⟩, 2, 2⟩

-- The searched middle lies between the reservations. Either fixed stub can
-- still intersect a glyph, and therefore must invalidate the complete route.
#guard match findRoute .y stubEnds [textObstacle .y ⟨29, 5, 1, 1⟩] 5 [2, 0] with
  | .error .domain => true
  | _ => false
#guard match findRoute .y stubEnds [textObstacle .y ⟨39, 5, 1, 1⟩] 5 [2, 0] with
  | .error .domain => true
  | _ => false

-- Vector routing retains its original obstacle inventory and complete route.
#guard (textObstacles .y { textScene with options := { profile := .vector } }).isEmpty
#guard findRoute .y stubEnds [] 5 [2, 0] == .ok [⟨29, 5⟩, ⟨40, 5⟩]

-- Line placement uses floor division for negative odd gaps and does not clip
-- supplied lines to the declared height. A space still occupies a cell.
#guard (Text.Place.positionedLines
  { centeredText with rect := ⟨10, 5, 0, 0⟩
    lines := [[⟨"ABC", false, false⟩], [⟨" ", false, false⟩]] }).map (·.rect) ==
  [⟨8, 5, 3, 1⟩, ⟨9, 6, 1, 1⟩]

-- Joined runs are sanitized before measuring, so a terminal control reserves
-- the replacement glyph that placement will attempt.
#guard (Text.Place.positionedLines
  { centeredText with align := .start
    lines := [[⟨"A", false, false⟩, ⟨String.singleton (Char.ofNat 0x85), false, false⟩]] }).map
  (·.rect) == [⟨10, 5, 2, 1⟩]

end Elegant.Layered.LaneBands
