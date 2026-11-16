import Elegant.Chart.WardleyConsts
import Elegant.Kinds.Common

set_option autoImplicit false

namespace Elegant.Kinds.Wardley

open Chart.Wardley

private def nonnegative (xs : List Int) : Bool := xs.all (fun x => 0 ≤ x)

private def decodeRegion (input : Input) (r : ModelRegionSet) : Except LayoutError Input := do
  let xs := r.regions
  match xs with
  | [] => return input
  | 0 :: stages :: boundaries :: values =>
      if stages < 0 ∨ boundaries < 0 ∨ values.length ≠ boundaries.toNat then
        throw .domain
      return { input with stageCount := stages.toNat, boundaries := values }
  | 1 :: flags :: strategy :: x :: y :: ox :: oy :: _ =>
      if flags < 0 ∨ strategy < 0 ∨ 4 < strategy then throw .domain
      return { input with nodes := input.nodes ++
        [⟨flags.toNat, strategy.toNat, x, y, unzigzag ox, unzigzag oy⟩] }
  | 2 :: parent :: count :: children =>
      if parent < 0 ∨ count < 0 ∨ children.length ≠ count.toNat ∨ !nonnegative children then
        throw .domain
      return { input with pipelines := input.pipelines ++
        [⟨parent.toNat, children.map Int.toNat⟩] }
  | 3 :: node :: x :: y :: _ =>
      if node < 0 then throw .domain
      return { input with trends := input.trends ++ [⟨node.toNat, x, y⟩] }
  | 4 :: x :: y :: _ =>
      return { input with accelerators := input.accelerators ++ [⟨x, y⟩] }
  | 5 :: x :: y :: _ =>
      return { input with deaccelerators := input.deaccelerators ++ [⟨x, y⟩] }
  | 6 :: _number :: x :: y :: _ =>
      return { input with annotations := input.annotations ++ [⟨x, y⟩] }
  | 7 :: x :: y :: _ => return { input with box := some ⟨x, y⟩ }
  | 8 :: x :: y :: _ => return { input with notes := input.notes ++ [⟨x, y⟩] }
  | _ => throw .domain

def decode (m : Model) : Except LayoutError Input := do
  let input ← m.regionSets.foldlM decodeRegion {}
  if input.trends.any (fun t => input.nodes.length ≤ t.node) ∨
      input.pipelines.any (fun p => input.nodes.length ≤ p.parent ∨ p.children.isEmpty ∨
        p.children.any (fun i => input.nodes.length ≤ i)) then
    throw .domain
  return input

private def modelBox (id parent : String) : ModelBox :=
  { id, parent, exclusive := false }

/-- Reconstruct only the model-stage containment schema, without computing any geometry. -/
def expectedBoxes (input : Input) (m : Model) : List ModelBox :=
  let nodes := input.nodes.zipIdx.map fun (n, i) =>
    let parent := if n.flags &&& 4 != 0 then "plot" else
      match input.pipelines.zipIdx.find? (fun (p, _) => p.children.contains i) with
      | some (_, k) => "pl" ++ toString k
      | none => "plot"
    modelBox ("n" ++ toString i) parent
  let indexed := fun (stem : String) (count : Nat) (parent : String) =>
    (List.range count).map (fun i => modelBox (stem ++ toString i) parent)
  let shownBox := input.box.isSome && m.labels.any (fun l =>
    (indexAfter "an" ".text" l.id).isSome && l.text != "")
  [modelBox "plot" ""] ++ indexed "pl" input.pipelines.length "plot" ++ nodes ++
    indexed "tg" input.trends.length "plot" ++ indexed "ac" input.accelerators.length "" ++
    indexed "de" input.deaccelerators.length "" ++ indexed "an" input.annotations.length "plot" ++
    if shownBox then [modelBox "ab" ""] else []

/-- This test is deliberately independent of the produced scene. -/
def modelConsistent (input : Input) (m : Model) : Bool :=
  m.boxes.all fun b =>
    match (expectedBoxes input m).find? (fun expected => expected.id == b.id) with
    | some expected => b.parent == expected.parent
    | none => true

def metadataConsistent (m : Model) : Bool :=
  m.boxes.all (fun b => !b.exclusive && b.role == .node) &&
    m.routes.all (fun r => !r.orthogonal) &&
    match Chart.Wardley.configured m "padding" with
    | none => true
    | some n => 0 ≤ n

def noSelfMembership (input : Input) : Bool :=
  input.pipelines.all (fun pipeline => !pipeline.children.contains pipeline.parent)

def parentsMarked (input : Input) : Bool :=
  input.pipelines.all fun pipeline =>
    match input.nodes[pipeline.parent]? with
    | some node => node.flags &&& 4 != 0
    | none => false

def scene (m : Model) : Except LayoutError Scene := do
  let input ← decode m
  if !(modelConsistent input m) then throw .domain
  if !(metadataConsistent m) then throw .domain
  if !(noSelfMembership input) then throw .domain
  if !(parentsMarked input) then throw .domain
  Chart.Wardley.layoutWith (Chart.Wardley.constants m) input m

def annotationParentsValid (m : Model) : Bool :=
  m.boxes.all fun b => b.id != "ab" || b.parent == ""

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  if annotationParentsValid m then
    match scene m with
    | .error e => .error (.geometry e)
    | .ok s => .ok { scene := s, budgetExhausted := false }
  else .error (.geometry .domain)

theorem decode_pipeline_bounds (m : Model) (input : Input)
    (h : decode m = .ok input) :
    ∀ pipeline ∈ input.pipelines,
      pipeline.parent < input.nodes.length ∧
      pipeline.children ≠ [] ∧
      ∀ i ∈ pipeline.children, i < input.nodes.length := by
  unfold decode at h
  cases hs : m.regionSets.foldlM decodeRegion {} with
  | error e => simp [hs, Bind.bind, Except.bind] at h
  | ok decoded =>
      simp only [hs, Bind.bind, Except.bind] at h
      by_cases hbad : decoded.trends.any (fun t => decoded.nodes.length ≤ t.node) ∨
          decoded.pipelines.any (fun p =>
            decoded.nodes.length ≤ p.parent ∨ p.children.isEmpty ∨
              p.children.any (fun i => decoded.nodes.length ≤ i))
      · exact False.elim (Common.guarded_error hbad h)
      · rw [ite_eq_right hbad] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst input
        intro pipeline hp
        have hclear : ¬ (decoded.nodes.length ≤ pipeline.parent ∨
            pipeline.children.isEmpty ∨
              pipeline.children.any (fun i => decoded.nodes.length ≤ i)) := by
          intro hinvalid
          apply hbad
          right
          exact List.any_eq_true.mpr ⟨pipeline, hp, by simpa using hinvalid⟩
        refine ⟨?_, ?_, ?_⟩
        · omega
        · intro hempty
          apply hclear
          right
          left
          simp [hempty]
        · intro i hi
          have hlt : ¬ decoded.nodes.length ≤ i := by
            intro hle
            apply hclear
            right
            right
            exact List.any_eq_true.mpr ⟨i, hi, by simpa using hle⟩
          omega

theorem decode_pipeline_first_index (m : Model) (input : Input)
    (h : decode m = .ok input) :
    ∀ pipeline ∈ input.pipelines,
      pipeline.children.headD 0 < input.nodes.length := by
  intro pipeline hp
  obtain ⟨_, hnonempty, hchildren⟩ := decode_pipeline_bounds m input h pipeline hp
  cases hc : pipeline.children with
  | nil => exact False.elim (hnonempty hc)
  | cons first rest =>
      have hfirst : first ∈ pipeline.children := by rw [hc]; exact List.mem_cons_self
      simpa [hc] using hchildren first hfirst

end Elegant.Kinds.Wardley
