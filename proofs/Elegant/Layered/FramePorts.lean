import Elegant.Layered.Normalize
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered.FramePorts

structure Span where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr, Inhabited

def checked (v : Int) : Except LayoutError Int :=
  if v < I32_MIN ∨ I32_MAX < v then .error .overflow else .ok v

def borderSpan (center width : Int) : Except LayoutError Span := do
  if width < 0 then throw .domain
  let lo ← checked (center - Int.fdiv width 2)
  let hi ← checked (lo + width)
  return { lo, hi }

def bounds (p : Proper) (x : List Int) (cluster : Nat) : Except LayoutError Span := do
  if x.length ≠ p.nodes.length then throw .domain
  let selected := (List.range p.nodes.length).filter fun i =>
    let n := (p.nodes.getD i default).node
    (n.border == -1 || n.border == 1) && n.clusterPath.getLast? == some cluster
  let spans ← selected.mapM fun i =>
    borderSpan (x.getD i 0) (p.nodes.getD i default).node.w
  match spans with
  | [] => throw .domain
  | s :: ss => return ss.foldl (fun a b => { lo := min a.lo b.lo, hi := max a.hi b.hi }) s

def portValue (s : Span) (index count : Nat) : Int :=
  s.lo + Int.fdiv (((index : Int) + 1) * (s.hi - s.lo)) ((count : Int) + 1)

def port (s : Span) (index count : Nat) : Except LayoutError Int :=
  if s.hi < s.lo ∨ count ≤ index then .error .domain
  else if ((index : Int) + 1) * (s.hi - s.lo) > 9223372036854775807 then .error .overflow
  else checked (portValue s index count)

/-- The caller supplies distinct neighbours in stable x/declaration order. Repeated
edge triples use the same index and therefore exactly the same boundary port. -/
def neighbourPort (s : Span) (neighbours : List Nat) (neighbour : Nat) :
    Except LayoutError Int :=
  port s (neighbours.idxOf neighbour) neighbours.length

/-- A top endpoint whose adjacent channel is inside its frame follows the leading
outer boundary. Outside approaches keep the ordinary stub. The caller reverses
this list for a target end and removes consecutive duplicates when joining runs. -/
def topStub (portX frameLeft frameTop channelY : Int) : List Point :=
  if frameTop < channelY then
    [{ x := portX, y := frameTop }, { x := frameLeft, y := frameTop },
      { x := frameLeft, y := channelY }]
  else [{ x := portX, y := frameTop }, { x := portX, y := channelY }]

def runX (portX frameLeft frameTop channelY : Int) : Int :=
  if frameTop < channelY then frameLeft else portX

theorem neighbourPort_same_triple (s : Span) (neighbours : List Nat) (n : Nat) :
    neighbourPort s neighbours n = port s (neighbours.idxOf n) neighbours.length := rfl

theorem port_uses_outer_bounds (s : Span) (i k : Nat) :
    portValue s i k =
      s.lo + Int.fdiv (((i : Int) + 1) * (s.hi - s.lo)) ((k : Int) + 1) := rfl

theorem port_between (s : Span) (i k : Nat) (h : s.lo ≤ s.hi) (hik : i < k) :
    s.lo ≤ portValue s i k ∧ portValue s i k ≤ s.hi := by
  unfold portValue
  have hn : 0 ≤ ((i : Int)+1)*(s.hi-s.lo) :=
    Int.mul_nonneg (by omega) (by omega)
  have hm : ((i : Int)+1)*(s.hi-s.lo) ≤ ((k : Int)+1)*(s.hi-s.lo) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  have hl := Int.ediv_nonneg hn (show 0 ≤ (k : Int)+1 by omega)
  have hu := Int.ediv_le_of_le_mul (show 0 < (k : Int)+1 by omega)
    (show ((i : Int)+1)*(s.hi-s.lo) ≤ (s.hi-s.lo)*((k : Int)+1) by
      simpa [Int.mul_comm] using hm)
  omega


def proxyRect (s : Span) (top height : Int) : Rect :=
  { x := s.lo, y := top, w := s.hi - s.lo, h := height }

theorem port_ok {s : Span} {i k : Nat} {px : Int} (h : port s i k = .ok px) :
    px = portValue s i k ∧ s.lo ≤ s.hi ∧ i < k := by
  unfold port at h
  split at h
  · simp at h
  · next hd =>
    split at h
    · simp at h
    · unfold checked at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        exact ⟨h.symm, by omega, by omega⟩

theorem port_on_proxy_boundary {s : Span} {i k : Nat} {px : Int}
    (h : port s i k = .ok px) (top height : Int) (hh : 0 ≤ height) :
    Validator.onBoundary { x := px, y := top } (proxyRect s top height) ∧
      Validator.onBoundary { x := px, y := top + height } (proxyRect s top height) := by
  obtain ⟨rfl, hs, hik⟩ := port_ok h
  obtain ⟨hl, hu⟩ := port_between s i k hs hik
  simp only [Validator.onBoundary, proxyRect]
  constructor <;> refine ⟨hl, by omega, by omega, by omega, ?_⟩
  · exact Or.inr (Or.inr (Or.inl True.intro))
  · exact Or.inr (Or.inr (Or.inr True.intro))
end Elegant.Layered.FramePorts
