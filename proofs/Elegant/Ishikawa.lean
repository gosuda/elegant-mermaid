import Elegant.Tree
import ElegantGeometry.Disjoint

set_option autoImplicit false
namespace Elegant.Ishikawa

structure Params where
  (spineBase ribMin ribPool spacing stub base perChild inset cos sin : Int)

structure Entry where
  node : Nat
  parent : Int
  depth : Nat

structure Rib where
  cause : Nat
  upper : Bool
  entries : List Entry := []
  order : List Nat := []
  heights : Int := 0
  length : Int := 0
  pieces : List (Nat × Rect × List Point) := []

structure Bone where
  x0 : Int := 0
  t0 : Int := 0
  x1 : Int := 0
  t1 : Int := 0
  count : Int := 0
  drawn : Int := 0

 def upper (index : Nat) : Bool := index % 2 == 0
def children (ns : List Tree.Node) (i : Nat) : List Nat :=
  (List.range ns.length).filter fun j => (ns[j]?).any (fun n => n.parent == some i)

def flatten (ns : List Tree.Node) (up : Bool) : Nat → List Nat → Int → Nat → List Entry → List Nat → List Entry × List Nat
  | 0, _, _, _, es, os => (es, os)
  | fuel + 1, ids, par, depth, es, os =>
    (if up then ids.reverse else ids).foldl (fun (es, os) node =>
      let idx := es.length
      let es := es ++ [⟨node, par, depth⟩]
      let os := if depth % 2 == 0 then os ++ [idx] else os
      let (es, os) := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
      (es, if depth % 2 == 0 then os else os ++ [idx])) (es, os)

def run (p : Params) (rise : Int) : Int := Int.fdiv (rise * p.cos) p.sin

def ordinate (spine : Int) (up : Bool) (t : Int) : Int := if up then spine - t else spine + t

def boneLength (p : Params) (count margin : Int) : Int :=
  max (if count > 0 then p.base + count * p.perChild else p.stub) ((count + 1) * margin)

def depthBone (p : Params) (par : Bone) (depth : Nat) (t count margin : Int) : Bone :=
  if depth % 2 != 0 then
    let x0 := par.x0 + Int.fdiv ((par.x1 - par.x0) * (par.count - par.drawn)) (par.count + 1)
    { x0, t0 := par.t0, x1 := x0 - run p (t - par.t0), t1 := t, count }
  else
    let x0 := par.x0 + Int.fdiv ((par.x1 - par.x0) * (t - par.t0)) (par.t1 - par.t0)
    { x0, t0 := t, x1 := x0 - boneLength p count margin, t1 := t, count }

def place (ns : List Tree.Node) (p : Params) (spine : Int) (r : Rib) : Except LayoutError Rib := do
  let some cause := ns[r.cause]? | throw .domain
  let x := -run p r.length
  let y := ordinate spine r.upper r.length
  let rect : Rect := ⟨x - Int.fdiv cause.width 2, if r.upper then y - cause.height else y, cause.width, cause.height⟩
  let mut pieces := [(r.cause, rect, [⟨0, spine⟩, ⟨x, y⟩])]
  let mut bones : List Bone := [{ x1 := x, t1 := r.length, count := (children ns r.cause).length }]
  let times := r.order.zipIdx
  let margin := run p r.heights + 3
  for (e, idx) in r.entries.zipIdx do
    let bi := (e.parent + 1).toNat
    let some par := bones[bi]? | throw .domain
    let some position := times.find? (fun v => v.1 == idx) | throw .domain
    let t := Int.fdiv (r.length * (position.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let count : Int := (children ns e.node).length
    if e.depth % 2 == 0 && par.t1 ≤ par.t0 then throw .domain
    let b := depthBone p par e.depth t count margin
    if e.depth % 2 != 0 then
      bones := bones.set bi { par with drawn := par.drawn + 1 }
    bones := bones ++ [b]
    let some n := ns[e.node]? | throw .domain
    let ey := ordinate spine r.upper b.t1
    pieces := pieces ++ [(e.node, ⟨b.x1 - n.width, ey - Int.fdiv n.height 2, n.width, n.height⟩,
      [⟨b.x0, ordinate spine r.upper b.t0⟩, ⟨b.x1, ey⟩])]
  return { r with pieces }

def extent (rs : List Rib) : Int × Int :=
  let pieces := rs.flatMap (·.pieces)
  let first := pieces.headD (0, ⟨0,0,0,0⟩, [])
  pieces.foldl (fun (l, right) v => (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) (first.2.1.x, 0)

def assemblePairs (spine : Int) : List Rib → Int → Int → Tree.Layout → Except LayoutError Tree.Layout
  | [], _, _, out => pure out
  | a :: rest, ceiling, previous, out => do
    let pair := a :: rest.take 1
    let (left, reach) := extent pair
    let attach := min ceiling (previous - reach)
    let mut out := out
    for r in pair do
      for (i, rect, points) in r.pieces do
        let rect := { rect with x := rect.x + attach }
        let points := points.map fun q => ({ x := q.x + attach, y := q.y } : Point)
        if !Tree.inLimit rect.x || !Tree.inLimit rect.y || !Tree.inLimit (rect.x + rect.w) || !Tree.inLimit (rect.y + rect.h) ||
            points.any (fun q => !Tree.inLimit q.x || !Tree.inLimit q.y) then throw .overflow
        out := { boxes := out.boxes.set i rect, routes := out.routes.set i points }
    let previous := attach + left
    out := { out with routes := out.routes.set 0 [⟨previous, spine⟩, ⟨0, spine⟩] }
    assemblePairs spine (rest.drop 1) previous previous out
termination_by rs _ _ _ => rs.length

def layout (ns : List Tree.Node) (p : Params) : Except LayoutError Tree.Layout := do
  if ns.isEmpty then return ⟨[], []⟩
  if !Tree.link ns || ns.any (fun n => n.width < 1 || n.height < 1) then throw .domain
  if p.spineBase < 5 || p.ribMin < 5 || p.ribPool < 1 || p.spacing < 1 || p.stub < 1 || p.base < 1 || p.perChild < 0 || p.inset < 0 || p.cos < 0 || p.sin < 1 then throw .domain
  let mut ribs := []
  for (cause, k) in (children ns 0).zipIdx do
    let (entries, order) := flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []
    let heights := entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0
    ribs := ribs ++ [({ cause, upper := upper k, entries, order, heights } : Rib)]
  let total (up : Bool) : Int := ((ribs.filter (fun r => r.upper == up)).map (fun r => (r.entries.length : Int))).sum
  let all := total true + total false
  let length (up : Bool) :=
    let initial := if all > 0 then max p.ribMin (Int.fdiv (p.ribPool * total up) all) else p.spineBase
    (ribs.filter (fun r => r.upper == up)).foldl (fun l r =>
      if r.entries.isEmpty then l else max l (max ((r.entries.length : Int) * p.spacing) ((r.entries.length + 1 : Nat) * r.heights))) initial
  let spine := max (length true) p.spineBase
  let placedRibs ← ribs.mapM fun r => do
    let ribLength := if (children ns r.cause).isEmpty then Int.fdiv (length r.upper) 5 else length r.upper
    place ns p spine { r with length := ribLength }
  let some head := ns[0]? | throw .domain
  let boxes := (List.replicate ns.length (⟨0,0,0,0⟩ : Rect)).set 0 ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩
  assemblePairs spine placedRibs (-p.inset) 0 ⟨boxes, List.replicate ns.length []⟩

theorem ishikawa_causes_alternate (i : Nat) : upper i = true ↔ i % 2 = 0 := by
  simp [upper]

theorem ishikawa_causes_alternate_next (i : Nat) :
    upper (i + 1) = !upper i := by
  have h := Nat.mod_lt i (by decide : 0 < 2)
  by_cases hi : i % 2 = 0
  · have hn : (i + 1) % 2 = 1 := by omega
    simp [upper, hi, hn]
  · have hi' : i % 2 = 1 := by omega
    have hn : (i + 1) % 2 = 0 := by omega
    simp [upper, hi', hn]

theorem pair_reach_before_previous (ceiling previous reach : Int) :
    min ceiling (previous - reach) + reach ≤ previous := by
  have h := Int.min_le_right ceiling (previous - reach)
  omega

theorem horizontal_bone_parallel (x t length : Int) :
    ((⟨x - length, t⟩ : Point).y - (⟨x, t⟩ : Point).y) = 0 := by
  simp

theorem diagonal_bone_run (p : Params) (x t0 t1 : Int) :
    ((⟨x - run p (t1 - t0), t1⟩ : Point).x - (⟨x, t0⟩ : Point).x) =
      -Int.fdiv ((t1 - t0) * p.cos) p.sin := by
  dsimp [run]
  omega

theorem pair_boxes_before_previous (ceiling previous reach : Int) (r : Rect)
    (hr : r.x + r.w ≤ reach) :
    (r.x + min ceiling (previous - reach)) + r.w ≤ previous := by
  have h := pair_reach_before_previous ceiling previous reach
  omega

theorem pair_boxes_disjoint (ceiling previous reach : Int) (a b : Rect)
    (ha : a.x + a.w ≤ reach) (hb : previous ≤ b.x) :
    Disjoint { a with x := a.x + min ceiling (previous - reach) } b := by
  have h := pair_boxes_before_previous ceiling previous reach a ha
  unfold Disjoint Rect.meetsInterior
  simp only
  omega

theorem extent_fold_right (pieces : List (Nat × Rect × List Point)) (initial : Int × Int)
    (piece : Nat × Rect × List Point) (hm : piece ∈ pieces) :
    piece.2.1.x + piece.2.1.w ≤
      (pieces.foldl (fun (l, right) v =>
        (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) initial).2 := by
  have grow : ∀ (ps : List (Nat × Rect × List Point)) (st : Int × Int),
      st.2 ≤ (ps.foldl (fun (l, right) v =>
        (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) st).2 := by
    intro ps
    induction ps with
    | nil => intro st; exact Int.le_refl _
    | cons p ps ih =>
      intro st
      exact Int.le_trans (Int.le_max_left _ _) (ih _)
  induction pieces generalizing initial with
  | nil => simp at hm
  | cons p ps ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst piece
      exact Int.le_trans (Int.le_max_right _ _) (grow ps _)
    · exact ih _ hm

theorem extent_fold_left (pieces : List (Nat × Rect × List Point)) (initial : Int × Int)
    (piece : Nat × Rect × List Point) (hm : piece ∈ pieces) :
    (pieces.foldl (fun (l, right) v =>
      (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) initial).1 ≤ piece.2.1.x := by
  have shrink : ∀ (ps : List (Nat × Rect × List Point)) (st : Int × Int),
      (ps.foldl (fun (l, right) v =>
        (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) st).1 ≤ st.1 := by
    intro ps
    induction ps with
    | nil => intro st; exact Int.le_refl _
    | cons p ps ih =>
      intro st
      exact Int.le_trans (ih _) (Int.min_le_left _ _)
  induction pieces generalizing initial with
  | nil => simp at hm
  | cons p ps ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst piece
      exact Int.le_trans (shrink ps _) (Int.min_le_right _ _)
    · exact ih _ hm

theorem extent_piece_bounds (rs : List Rib) (piece : Nat × Rect × List Point)
    (hm : piece ∈ rs.flatMap (·.pieces)) :
    (extent rs).1 ≤ piece.2.1.x ∧
      piece.2.1.x + piece.2.1.w ≤ (extent rs).2 := by
  exact ⟨extent_fold_left _ _ _ hm, extent_fold_right _ _ _ hm⟩

theorem pair_slots_disjoint (earlier later : List Rib)
    (ceiling previous laterAttach : Int)
    (a b : Nat × Rect × List Point)
    (ha : a ∈ earlier.flatMap (·.pieces))
    (hb : b ∈ later.flatMap (·.pieces))
    (hprevious : previous = laterAttach + (extent later).1) :
    Disjoint
      { a.2.1 with x := a.2.1.x + min ceiling (previous - (extent earlier).2) }
      { b.2.1 with x := b.2.1.x + laterAttach } := by
  apply pair_boxes_disjoint
  · exact (extent_piece_bounds earlier a ha).2
  · have hleft := (extent_piece_bounds later b hb).1
    simp only
    omega

theorem ishikawa_ribs_ordered (rs : List Rib) (ceiling previous : Int)
    (piece : Nat × Rect × List Point) (hm : piece ∈ rs.flatMap (·.pieces)) :
    let attach := min ceiling (previous - (extent rs).2)
    piece.2.1.x + attach + piece.2.1.w ≤ previous := by
  apply pair_boxes_before_previous
  exact extent_fold_right _ _ _ hm

theorem ishikawa_subcause_parallel (p : Params) (par : Bone) (depth : Nat)
    (t count margin spine : Int) (up : Bool) :
    let b := depthBone p par depth t count margin
    (depth % 2 = 0 →
      ordinate spine up b.t0 = ordinate spine up b.t1 ∧
      b.x1 - b.x0 = -boneLength p count margin) ∧
    (depth % 2 ≠ 0 →
      b.t0 = par.t0 ∧ b.t1 = t ∧
      b.x1 - b.x0 = -Int.fdiv ((t - par.t0) * p.cos) p.sin) := by
  dsimp
  by_cases h : depth % 2 = 0
  · simp [depthBone, h] <;> omega
  · have hodd : depth % 2 = 1 := by omega
    simp [depthBone, hodd, run] <;> omega

theorem depthBone_even_endpoints (p : Params) (par : Bone) (depth : Nat)
    (t count margin : Int) (h : depth % 2 = 0) :
    (depthBone p par depth t count margin).t0 = t ∧
      (depthBone p par depth t count margin).t1 = t ∧
      (depthBone p par depth t count margin).x1 =
        (depthBone p par depth t count margin).x0 - boneLength p count margin := by
  simp [depthBone, h]

theorem depthBone_odd_endpoints (p : Params) (par : Bone) (depth : Nat)
    (t count margin : Int) (h : depth % 2 ≠ 0) :
    (depthBone p par depth t count margin).t0 = par.t0 ∧
      (depthBone p par depth t count margin).t1 = t ∧
      (depthBone p par depth t count margin).x0 =
        par.x0 + Int.fdiv ((par.x1 - par.x0) * (par.count - par.drawn)) (par.count + 1) ∧
      (depthBone p par depth t count margin).x1 =
        (depthBone p par depth t count margin).x0 - run p (t - par.t0) := by
  have hodd : depth % 2 = 1 := by omega
  simp [depthBone, hodd]

theorem opposite_cause_slots_disjoint (spine upperLength lowerLength : Int)
    (upperX lowerX upperWidth lowerWidth upperHeight lowerHeight : Int)
    (hu : 0 ≤ upperLength) (hl : 0 ≤ lowerLength) :
    Disjoint
      ⟨upperX, ordinate spine true upperLength - upperHeight, upperWidth, upperHeight⟩
      ⟨lowerX, ordinate spine false lowerLength, lowerWidth, lowerHeight⟩ := by
  simp [Disjoint, Rect.meetsInterior, ordinate] <;> omega

theorem subcause_slots_disjoint (spine t₀ t₁ heightBound : Int) (up : Bool)
    (x₀ x₁ width₀ width₁ height₀ height₁ : Int)
    (h₀ : 0 ≤ height₀) (_h₁ : 0 ≤ height₁)
    (hb₀ : height₀ ≤ heightBound) (hb₁ : height₁ ≤ heightBound)
    (hgap : t₀ + heightBound ≤ t₁) :
    Disjoint
      ⟨x₀, ordinate spine up t₀ - Int.fdiv height₀ 2, width₀, height₀⟩
      ⟨x₁, ordinate spine up t₁ - Int.fdiv height₁ 2, width₁, height₁⟩ := by
  rw [Tree.fdiv2, Tree.fdiv2]
  cases up <;> simp [Disjoint, Rect.meetsInterior, ordinate] <;> omega

theorem rib_piece_left_of_root (pieceX pieceW attach previous rootX rootW : Int)
    (py ph ry rh : Int)
    (hreach : pieceX + attach + pieceW ≤ previous) (hprev : previous ≤ rootX) :
    Disjoint ⟨pieceX + attach, py, pieceW, ph⟩ ⟨rootX, ry, rootW, rh⟩ := by
  simp [Disjoint, Rect.meetsInterior]
  omega
end Elegant.Ishikawa
