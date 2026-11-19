import Elegant.Railroad
import Elegant.Kinds.Common

set_option autoImplicit false

namespace Elegant.Kinds.Railroad

/-- The four front-end syntaxes already share the same lowered model dump. -/
def display (m : Model) (b : ModelBox) : String :=
  match m.labels.find? (fun l => l.owner == b.id) with
  | some l => l.text
  | none => b.text.getD b.id

def children (m : Model) (id : String) : List ModelBox :=
  m.boxes.filter (fun b => b.parent == id)

def decodeNode : Nat → Model → ModelBox → Except LayoutError Elegant.Railroad.Node
  | 0, _, _ => .error .domain
  | fuel+1, m, b => do
    let kids ← (children m b.id).mapM (decodeNode fuel m)
    let kind := if ["terminal", "nonterminal", "special", "sequence", "choice",
        "optional", "zeroOrMore", "oneOrMore"].contains b.shape then b.shape else "terminal"
    return ⟨b.id,kind,display m b,kids⟩

def decodeRule (m : Model) (b : ModelBox) : Except LayoutError Elegant.Railroad.Rule := do
  if b.shape == "rule" then
    match children m b.id with
    | [kid] => return ⟨b.id,display m b,← decodeNode (m.boxes.length+1) m kid⟩
    | _ => throw .domain
  else return ⟨"","",← decodeNode (m.boxes.length+1) m b⟩

def lower (m : Model) : Except LayoutError (List Elegant.Railroad.Rule) :=
  (children m "").mapM (decodeRule m)

/-- The arities written by `railroadTree` after all four native grammars have
lowered to their shared model. Rule containers are handled separately. -/
def NodeArity (m : Model) (b : ModelBox) : Prop :=
  match b.shape with
  | "terminal" | "nonterminal" | "special" => (children m b.id).length = 0
  | "sequence" | "choice" => 2 ≤ (children m b.id).length
  | "optional" | "zeroOrMore" | "oneOrMore" => (children m b.id).length = 1
  | _ => False

/-- Structural invariants of the actual model encoder in `internal/layout/railroad.go`.
`addRailroadRule` writes one root rule container and exactly one definition root.
`addRailroadNode` writes every definition in preorder with its parent's id, its closed
shape tag and its source arity. A decreasing rank is the reverse of that preorder;
it makes the finite-tree requirement explicit without mentioning the decoder's result.
These hypotheses concern normalization, not parsing or successful lowering. -/
structure Normalized (m : Model) : Prop where
  wellFormed : WellFormed m
  roots : ∀ b ∈ children m "", b.shape = "rule" ∧
    ∃ kid, children m b.id = [kid]
  nodeForms : ∀ b ∈ m.boxes, b.shape = "rule" ∨ NodeArity m b
  ruleRoots : ∀ b ∈ m.boxes, b.shape = "rule" → b.parent = ""
  roles : ∀ b ∈ m.boxes,
    (b.shape = "terminal" ∨ b.shape = "nonterminal" ∨ b.shape = "special") →
      b.role = .node ∧ b.exclusive = true
  groups : ∀ b ∈ m.boxes,
    ¬ (b.shape = "terminal" ∨ b.shape = "nonterminal" ∨ b.shape = "special") →
      b.role = .group ∧ b.exclusive = false
  ranked : ∃ rank : String → Nat,
    (∀ b ∈ m.boxes, rank b.id < m.boxes.length) ∧
    ∀ b ∈ m.boxes, ∀ child ∈ children m b.id, rank child.id < rank b.id

theorem mapM_total {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ y, f x = .ok y) →
      ∃ ys, xs.mapM f = .ok ys := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[],rfl⟩
  | cons x xs ih =>
    intro h
    obtain ⟨y,hy⟩ := h x (by simp)
    obtain ⟨ys,hys⟩ := ih (fun a ha => h a (by simp [ha]))
    exact ⟨y::ys,by simp [List.mapM_cons,hy,hys,bind,Except.bind,pure,Except.pure]⟩

theorem decodeNode_total (m : Model) (rank : String → Nat)
    (hr : ∀ b ∈ m.boxes, ∀ child ∈ children m b.id, rank child.id < rank b.id) :
    ∀ (fuel : Nat) (b : ModelBox), b ∈ m.boxes → rank b.id < fuel →
      ∃ n, decodeNode fuel m b = .ok n := by
  intro fuel
  induction fuel with
  | zero => intro b _ h; omega
  | succ fuel ih =>
    intro b hb hbound
    obtain ⟨nodes,hnodes⟩ := mapM_total (decodeNode fuel m) (children m b.id)
      (fun child hc => ih child (List.mem_filter.mp hc).1
        (by have := hr b hb child hc; omega))
    refine ⟨⟨b.id,
      if ["terminal","nonterminal","special","sequence","choice","optional",
          "zeroOrMore","oneOrMore"].contains b.shape then b.shape else "terminal",
      display m b,nodes⟩,?_⟩
    simp [decodeNode,hnodes,bind,Except.bind,pure,Except.pure]

/-- Every structurally valid normalized frontend model lowers to a rule forest,
not merely to an arbitrary `Except` result. All four source syntaxes share this
model-stage boundary; the native grammar checks remain outside the Lean reference. -/
theorem railroad_lower_total (m : Model) (hm : Normalized m) :
    ∃ rules, lower m = .ok rules := by
  obtain ⟨rank,hrange,hchildren⟩ := hm.ranked
  unfold lower
  apply mapM_total
  intro b hb
  obtain ⟨hshape,kid,hkid⟩ := hm.roots b hb
  have hmem : kid ∈ m.boxes := (List.mem_filter.mp
    (show kid ∈ children m b.id by rw [hkid]; simp)).1
  obtain ⟨node,hnode⟩ := decodeNode_total m rank hchildren (m.boxes.length+1) kid hmem
    (by have := hrange kid hmem; omega)
  refine ⟨⟨b.id,display m b,node⟩,?_⟩
  simp [decodeRule,hshape,hkid,hnode,bind,Except.bind,pure,Except.pure]

def textBytes (m : Model) : Nat :=
  let unlabeled := m.boxes.foldl (fun n b =>
    if m.labels.any (fun l => l.owner == b.id) then n
    else n + (b.text.getD "").utf8ByteSize) 0
  m.labels.foldl (fun n l => n+l.text.utf8ByteSize) unlabeled

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  let limits := m.options.limits
  if m.boxes.length > limits.maxNodes then
    throw (.tooLarge limits.maxNodes m.boxes.length)
  if m.routes.length > limits.maxEdges then
    throw (.tooLarge limits.maxEdges m.routes.length)
  if textBytes m > limits.maxTextBytes then
    throw (.tooLarge limits.maxTextBytes (textBytes m))
  if m.routes.any (fun r => m.boxes.any (fun b => b.id == r.id)) then
    throw (.geometry .domain)
  let rules ← (lower m).mapError LayoutFailure.geometry
  let scene ← (Elegant.Railroad.layout m rules).mapError LayoutFailure.geometry
  return {scene := scene.projectCellAttachments (Common.routeMarkers m), budgetExhausted := false}

end Elegant.Kinds.Railroad
