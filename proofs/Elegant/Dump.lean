import Elegant.Scene
import Elegant.Gen.Markers
import Lean

namespace Elegant

private def field (j : Lean.Json) (k : String) : Except String Lean.Json := j.getObjVal? k
private def str (j : Lean.Json) (k : String) : Except String String := field j k >>= Lean.Json.getStr?
private def nat (j : Lean.Json) (k : String) : Except String Nat := field j k >>= Lean.Json.getNat?
private def bool (j : Lean.Json) (k : String) : Except String Bool := field j k >>= Lean.Json.getBool?
private def arr (j : Lean.Json) (k : String) : Except String (List Lean.Json) := do
  return (← (← field j k).getArr?).toList

private def profile (s : String) : Except String Profile :=
  match s with
  | "vector" => .ok .vector | "cell" => .ok .cell
  | _ => .error "invalid profile"

private def direction (s : String) : Except String Direction :=
  match s with
  | "TB" => .ok .TB | "BT" => .ok .BT | "LR" => .ok .LR | "RL" => .ok .RL
  | _ => .error "invalid direction"

private def configValue (j : Lean.Json) : Except String ConfigValue :=
  match j with
  | .str s => .ok (.string s)
  | .bool b => .ok (.boolean b)
  | _ => return .integer (← j.getInt?)

private def readOptions (j : Lean.Json) : Except String Options := do
  let limits ← field j "limits"
  let entries ← j.getObj?
  let extras := entries.toList.filter (fun p =>
    !["profile", "thoroughness", "max_width", "direction", "limits"].contains p.1)
  let config ← extras.mapM fun (k, v) => return (k, ← configValue v)
  return { profile := (← profile (← str j "profile"))
           thoroughness := (← nat j "thoroughness")
           maxWidth := (← nat j "max_width")
           direction := (← direction (← str j "direction"))
           limits := ⟨← nat limits "max_nodes", ← nat limits "max_edges", ← nat limits "max_text_bytes"⟩
           config := config }

private def exclude (j : Lean.Json) (keys : List String) : Except String Unit := do
  if keys.any (fun k => (j.getObjVal? k).isOk) then
    throw "coordinate data in model stage"

private def optStr (j : Lean.Json) (k dflt : String) : Except String String :=
  match j.getObjVal? k with
  | .ok v => v.getStr?
  | .error _ => .ok dflt

private def readBox (kind : String) (j : Lean.Json) : Except String ModelBox := do
  exclude j ["x", "y", "w", "h"]
  let role ← str j "role"
  let role ← match role with
    | "node" => pure BoxRole.node | "group" => pure BoxRole.group
    | _ => throw "invalid box role"
  let ownDirection ←
    match j.getObjVal? "direction" with
    | .ok value => value.getStr?
    | .error _ => pure ""
  let accepted := ["TB", "BT", "LR", "RL"] ++ (if kind == "sequence" then ["w", "n"] else [])
  if role == .group && ownDirection != "" && !accepted.contains ownDirection then
    throw "invalid group direction"
  let text ← match j.getObjVal? "text" with
    | .ok value => some <$> value.getStr?
    | .error _ => pure none
  let icon ← match j.getObjVal? "icon" with
    | .ok _ => bool j "icon"
    | .error _ => pure false
  return { id := (← str j "id")
           role := role
           parent := (← str j "parent")
           exclusive := (← bool j "exclusive")
           direction := ownDirection
           shape := (← optStr j "shape" "")
           icon := icon
           text := text }

private def markerName (s : String) : Except String String :=
  if s == "none" || markers.any (fun m => m.name == s) then .ok s else .error "invalid marker"

private def strokeName (s : String) : Except String String :=
  if ["normal", "solid", "thick", "dotted", "dashed", "invisible"].contains s then .ok s
  else .error "invalid stroke"

private def sideOf (s : String) : Except String Side :=
  match s with
  | "" => .ok .none | "T" => .ok .top | "B" => .ok .bottom | "L" => .ok .left | "R" => .ok .right
  | _ => .error "invalid side"

private def readRoute (j : Lean.Json) : Except String ModelRoute := do
  exclude j ["points"]
  let markerStart ← markerName (← optStr j "marker_start" "none")
  let markerEnd ← markerName (← optStr j "marker_end" "point")
  let stroke ← strokeName (← optStr j "stroke" "normal")
  let minLength ← match j.getObjVal? "min_length" with
    | .ok value => value.getInt?
    | .error _ => pure 1
  return { id := (← str j "id")
           fromId := (← str j "from")
           toId := (← str j "to")
           orthogonal := (← bool j "orthogonal")
           markerStart := markerStart
           markerEnd := markerEnd
           stroke := stroke
           fromSide := (← sideOf (← optStr j "from_side" ""))
           toSide := (← sideOf (← optStr j "to_side" ""))
           minLength := minLength }

private def readLabel (j : Lean.Json) : Except String ModelLabel := do
  exclude j ["x", "y", "w", "h"]
  let lines ← (← arr j "lines").mapM Lean.Json.getStr?
  if !lines.isEmpty then throw "model label lines must be empty"
  return ⟨← str j "id", ← str j "owner", ← str j "text", lines⟩

private def readRegionSet (j : Lean.Json) : Except String ModelRegionSet := do
  let values ← (← j.getArr?).toList.mapM Lean.Json.getInt?
  match values with
  | [] => throw "empty region set"
  | parent :: regions => return ⟨parent, regions⟩

private def readRegions (j : Lean.Json) : Except String (List ModelRegionSet) :=
  match j.getObjVal? "regions" with
  | .ok value => do (← value.getArr?).toList.mapM readRegionSet
  | .error _ => pure []

def readModel (source : String) : Except String Model := do
  let j ← Lean.Json.parse source
  exclude j ["canvas"]
  if (← nat j "version") != 1 then throw "unsupported version"
  if (← str j "stage") != "model" then throw "expected model stage"
  let p ← profile (← str j "profile")
  let options ← readOptions (← field j "options")
  if p != options.profile then throw "profile mismatch"
  let kind ← str j "kind"
  return { kind := kind
           profile := p
           options := options
           boxes := (← (← arr j "boxes").mapM (readBox kind))
           routes := (← (← arr j "routes").mapM readRoute)
           labels := (← (← arr j "labels").mapM readLabel)
           regionSets := (← readRegions j) }

private def escapeChar (c : Char) : String :=
  match c with
  | '"' => "\\\"" | '\\' => "\\\\" | '\t' => "\\t"
  | '\n' => "\\n" | '\r' => "\\r"
  | _ => if c.toNat == 8 then "\\b" else if c.toNat == 12 then "\\f" else
    if c.toNat < 32 then
      let hex := "0123456789abcdef".toList.toArray
      "\\u00" ++ String.singleton (hex[c.toNat / 16]!) ++ String.singleton (hex[c.toNat % 16]!)
    else String.singleton c

private def quote (s : String) : String := "\"" ++ String.join (s.toList.map escapeChar) ++ "\""
private def array (separator : String) (xs : List String) : String :=
  "[" ++ String.intercalate separator xs ++ "]"
private def member (k v : String) : String := quote k ++ ":" ++ v
private def object (xs : List String) : String := "{" ++ String.intercalate "," xs ++ "}"
private def boolean (b : Bool) : String := if b then "true" else "false"
private def configDump : ConfigValue → String
  | .integer i => toString i | .string s => quote s | .boolean b => boolean b
private def optionsDump (o : Options) : String := object (
  [member "profile" (quote o.profile.id), member "thoroughness" (toString o.thoroughness),
   member "max_width" (toString o.maxWidth), member "direction" (quote o.direction.id),
   member "limits" (object [member "max_nodes" (toString o.limits.maxNodes),
     member "max_edges" (toString o.limits.maxEdges),
     member "max_text_bytes" (toString o.limits.maxTextBytes)])] ++
   o.config.map (fun (k, v) => member k (configDump v)))
private def rectMembers (r : Rect) : List String :=
  [member "x" (toString r.x), member "y" (toString r.y),
   member "w" (toString r.w), member "h" (toString r.h)]
private def boxDump (b : Box) : String := object (
  [member "id" (quote b.id), member "role" (quote b.role)] ++ rectMembers b.rect ++
  [member "parent" (quote b.parent), member "exclusive" (boolean b.exclusive)])
private def routeDump (r : Route) : String := object
  [member "id" (quote r.id), member "from" (quote r.fromId), member "to" (quote r.toId),
   member "orthogonal" (boolean r.orthogonal), member "points" (array ","
     (r.points.map (fun p => array "," [toString p.x, toString p.y])))]
private def labelDump (l : SceneLabel) : String := object (
  [member "id" (quote l.id), member "owner" (quote l.owner), member "text" (quote l.text)] ++
  rectMembers l.rect ++ [member "lines" (array "," (l.lines.map quote))])

def toDump (s : Scene) : String :=
  "{" ++ String.intercalate ","
    [member "version" "1", member "stage" (quote "layout"), member "kind" (quote s.kind),
     member "profile" (quote s.profile.id), member "options" (optionsDump s.options),
     member "canvas" (object [member "w" (toString s.canvas.w), member "h" (toString s.canvas.h)])] ++
  ",\n" ++ member "boxes" (array ",\n" (s.boxes.map boxDump)) ++
  ",\n" ++ member "routes" (array ",\n" (s.routes.map routeDump)) ++
  ",\n" ++ member "labels" (array ",\n" (s.labels.map labelDump)) ++ "}\n"

end Elegant
