import Lean
import ElegantGeometry.Basic

namespace Elegant

inductive LayoutFailure where
  | geometry (error : LayoutError)
  | tooLarge (limit actual : Nat)
  deriving DecidableEq, Repr

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

inductive Side where
  | none | top | bottom | left | right
  deriving DecidableEq, Repr, Inhabited

def Side.id : Side → String
  | .none => "" | .top => "T" | .bottom => "B" | .left => "L" | .right => "R"

/-- `shape`, `icon`, and `text` are model-stage extras of the per-kind adapters: the shape token,
nonempty resolved icon presence, and box text when no `<id>.label` label exists (ER tables). -/
structure ModelBox where
  id : String
  role : BoxRole := .node
  parent : String := ""
  exclusive : Bool := true
  direction : String := ""
  shape : String := ""
  icon : Bool := false
  text : Option String := none
  deriving DecidableEq, Repr

/-- `fromSide` and `toSide` pin the port side at each end (`Side.none` leaves it free);
`minLength` is the minimum rank span the kind asks for. -/
structure ModelRoute where
  id : String
  fromId : String
  toId : String
  orthogonal : Bool := true
  markerStart : String := "none"
  markerEnd : String := "point"
  stroke : String := "normal"
  fromSide : Side := .none
  toSide : Side := .none
  minLength : Int := 1
  deriving DecidableEq, Repr

structure ModelLabel where
  id : String
  owner : String
  text : String
  lines : List String := []
  deriving DecidableEq, Repr

/-- One frontend region set, verbatim: its parent index and its region integers (`-1` for an absent
index). The kind defines the meaning (`spec/model-dump.md`, model-dump-25). -/
structure ModelRegionSet where
  parent : Int
  regions : List Int
  deriving DecidableEq, Repr

structure Model where
  kind : String
  profile : Profile := .vector
  options : Options := {}
  boxes : List ModelBox := []
  routes : List ModelRoute := []
  labels : List ModelLabel := []
  regionSets : List ModelRegionSet := []
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
    m.labels.all (fun l => boxes.contains l.owner || routes.contains l.owner) &&
    m.boxes.all (fun b => b.role != .group || !b.exclusive)

abbrev WellFormed (m : Model) : Prop := modelWellFormed m = true

namespace Model

private theorem eraseDups_length_le : ∀ l : List String, l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have h1 := eraseDups_length_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons]
    omega
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem nodup_of_eraseDups_length :
    ∀ l : List String, l.eraseDups.length = l.length → l.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: as => by
    intro h
    rw [List.eraseDups_cons] at h
    simp only [List.length_cons] at h
    have h1 := eraseDups_length_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    have hf : (as.filter fun b => !b == a).length = as.length := by omega
    have hall : ∀ b ∈ as, (!b == a) = true := List.length_filter_eq_length_iff.mp hf
    have hfe : (as.filter fun b => !b == a) = as := List.filter_eq_self.mpr hall
    have hn := nodup_of_eraseDups_length (as.filter fun b => !b == a) (by omega)
    rw [hfe] at hn
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, hn⟩
    have := hall a hmem
    simp at this
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem boxIds_nodup {m : Model} (h : WellFormed m) : (m.boxes.map (·.id)).Nodup := by
  unfold WellFormed modelWellFormed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  have hu' : ((m.boxes.map (·.id)).eraseDups.length == (m.boxes.map (·.id)).length) = true := hu
  exact nodup_of_eraseDups_length _ (beq_iff_eq.mp hu')


theorem routeIds_nodup {m : Model} (h : WellFormed m) : (m.routes.map (·.id)).Nodup := by
  unfold WellFormed modelWellFormed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, hr⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  have hr' : ((m.routes.map (·.id)).eraseDups.length == (m.routes.map (·.id)).length) = true := hr
  exact nodup_of_eraseDups_length _ (beq_iff_eq.mp hr')
end Model

def modelBoxText (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (fun l => l.owner == b.id && l.id == b.id ++ ".label") with
  | some l => l.text
  | none => b.id

def modelTextBytes (m : Model) : Nat :=
  let boxBytes := m.boxes.foldl (fun n b => n + (modelBoxText m b).utf8ByteSize) 0
  m.labels.foldl (fun n l =>
    if m.boxes.any (fun b => l.owner == b.id && l.id == b.id ++ ".label") then n
    else n + l.text.utf8ByteSize) boxBytes

abbrev WithinLimits (m : Model) : Prop :=
  m.boxes.length ≤ m.options.limits.maxNodes ∧
  m.routes.length ≤ m.options.limits.maxEdges ∧
  modelTextBytes m ≤ m.options.limits.maxTextBytes

end Elegant
