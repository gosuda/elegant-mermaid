import Lean

namespace Elegant

inductive Profile where
  | vector | cell
  deriving DecidableEq, Repr, Inhabited

def Profile.id : Profile → String
  | .vector => "vector"
  | .cell => "cell"

inductive Direction where
  | TB | BT | LR | RL
  deriving DecidableEq, Repr, Inhabited

def Direction.id : Direction → String
  | .TB => "TB" | .BT => "BT" | .LR => "LR" | .RL => "RL"

inductive BoxRole where
  | node | group
  deriving DecidableEq, Repr, Inhabited

def BoxRole.id : BoxRole → String
  | .node => "node" | .group => "group"

structure Limits where
  maxNodes : Nat := 2000
  maxEdges : Nat := 5000
  maxTextBytes : Nat := 1048576
  deriving DecidableEq, Repr, Inhabited

inductive ConfigValue where
  | integer (value : Int)
  | string (value : String)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

structure Options where
  profile : Profile := .vector
  thoroughness : Nat := 3
  maxWidth : Nat := 0
  direction : Direction := .TB
  limits : Limits := {}
  config : List (String × ConfigValue) := []
  deriving DecidableEq, Repr, Inhabited

structure ModelBox where
  id : String
  role : BoxRole := .node
  parent : String := ""
  exclusive : Bool := true
  deriving DecidableEq, Repr

structure ModelRoute where
  id : String
  fromId : String
  toId : String
  orthogonal : Bool := true
  deriving DecidableEq, Repr

structure ModelLabel where
  id : String
  owner : String
  text : String
  lines : List String := []
  deriving DecidableEq, Repr

structure Model where
  kind : String
  profile : Profile := .vector
  options : Options := {}
  boxes : List ModelBox := []
  routes : List ModelRoute := []
  labels : List ModelLabel := []
  deriving DecidableEq, Repr

private def parentTerminates (boxes : List ModelBox) : Nat → String → Bool
  | _, "" => true
  | 0, _ => false
  | n + 1, id =>
    match boxes.find? (fun b => b.id == id) with
    | none => false
    | some b => parentTerminates boxes n b.parent

private def unique (ids : List String) : Bool := ids.eraseDups.length == ids.length

def modelWellFormed (m : Model) : Bool :=
  let boxes := m.boxes.map (·.id)
  let routes := m.routes.map (·.id)
  unique boxes && unique routes && unique (m.labels.map (·.id)) &&
    m.boxes.all (fun b => parentTerminates m.boxes m.boxes.length b.parent) &&
    m.routes.all (fun r => boxes.contains r.fromId && boxes.contains r.toId) &&
    m.labels.all (fun l => boxes.contains l.owner || routes.contains l.owner)

abbrev WellFormed (m : Model) : Prop := modelWellFormed m = true

def modelTextBytes (m : Model) : Nat :=
  m.labels.foldl (fun n l => n + l.text.utf8ByteSize) 0

abbrev WithinLimits (m : Model) : Prop :=
  m.boxes.length ≤ m.options.limits.maxNodes ∧
  m.routes.length ≤ m.options.limits.maxEdges ∧
  modelTextBytes m ≤ m.options.limits.maxTextBytes

end Elegant
