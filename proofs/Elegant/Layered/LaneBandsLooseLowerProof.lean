import Elegant.Layered.LaneBandsLooseVictimProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-! Loose-band lower bound is false; corrected per-pair bound.

Verdict on `PinLooseRouteLower` (every kept loose-band route point at or above the loose content minimum): FALSE. Witness `mWit` with a labelled loose edge `e0 : o1 -> o2` beside one lane (`boxes [A, a1 in A, o1, o2]`, label `l0` on `e0` with 100 `Y` characters): base pin axis `x`, `sp.clear = 1792`, loose band `(start 11390, thickness 2640, shift 48, members [o1, o2])`, `lo = 13134`, route points `[14454, 14454, 8062, 8062, 8062, 8062, 14454, 14454]` so `8062 < lo` and `lower = false`, while pinned `c6 = true`. In def form `(bands[j1]).start + sp.clear ≤ axis.point p + (bands[j1]).shift` fails as `13182 ≤ 8110` with `(bands[j1]).start = 11390` and worst `axis.point p + shift = 8062 + 48 = 8110`. Five truth probes hold with `lower = true` (`self` loose self-loop, `above`/`below` loose self-loops around lanes, `emptyLane` empty lane plus loose self-loop, `nested` nested group plus loose self-loop, all with `c1 = true`; ill-formed input rejected by `layoutFamily`).

The true form the consumer `pinLooseRouteLaneVictimClear` needs is per-pair: a kept loose route stays above its own lane victim box end (shifted), not above the loose slot start. On `mWit` the dip `8062` still clears the exclusive lane victim `a1` (`a1` base `[2560, 4990]`, lane shift `3072`, loose shift `48`: shifted route minimum `8110` against shifted box end `8062`). `PinLooseRouteAboveLaneBox` is that narrower per-pair bound over executed runs (one public residual, true on the five probes and on `mWit` for every exclusive out-of-scope lane victim; per-pair probe `PinLooseLowerT_AboveBox` gives `above = true` on `self`, `above`, `below`, `emptyLane`, `nested`, `m01`, `m03`, `m05`, `m09`, `m12`, `m19` and `mWit`). -/
private theorem llLooseLower_shiftPoint_point (axis : Axis) (delta : Int) (p : Point) :
    axis.point (lvShiftPoint axis delta p) = axis.point p + delta := by
  cases axis <;> rfl

private theorem llLooseLower_shiftRect_start (axis : Axis) (delta : Int) (r : Rect) :
    axis.start (lvShiftRect axis delta r) = axis.start r + delta := by
  cases axis <;> rfl

private theorem llLooseLower_shiftRect_length (axis : Axis) (delta : Int) (r : Rect) :
    axis.length (lvShiftRect axis delta r) = axis.length r := by
  cases axis <;> rfl

private theorem llLooseLower_stripMiss {axis : Axis} {pts : List Point} {r : Rect} {Rlo : Int}
    (hroute : ∀ q ∈ pts, Rlo ≤ axis.point q)
    (hbox : axis.start r + axis.length r ≤ Rlo) : ¬ Polyline.hitsRect pts r := by
  have hall : Polyline.allSegsMiss pts r := by
    induction pts with
    | nil => trivial
    | cons p rest ih =>
      cases rest with
      | nil => trivial
      | cons q rest2 =>
        have hpm : p ∈ p :: q :: rest2 := List.mem_cons.mpr (Or.inl rfl)
        have hqm : q ∈ p :: q :: rest2 :=
          List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))
        have hp := hroute p hpm
        have hq := hroute q hqm
        refine ⟨?_, ih (fun p' hp' => hroute p' (List.mem_cons_of_mem _ hp'))⟩
        cases axis with
        | x =>
          simp only [Axis.point, Axis.start, Axis.length] at hp hq hbox ⊢
          exact Or.inr (Or.inl (by omega))
        | y =>
          simp only [Axis.point, Axis.start, Axis.length] at hp hq hbox ⊢
          exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  intro hhit
  obtain ⟨_, _, hmiss⟩ := hhit
  exact hmiss hall

/-- Narrower per-pair bound on the way: a loose-covered route stays above each exclusive out-of-scope lane victim box end (shifted). True on the five truth probes and on `mWit` (see header); the single open residual. -/
def PinLooseRouteAboveLaneBox (axis : Axis) (bands : List Band) (s : Scene) : Prop :=
  ∀ (old : Route), old ∈ s.routes →
    ∀ (b_old : Box), b_old ∈ s.boxes → b_old.exclusive = true →
      b_old.id ∉ s.layoutDump.routeScope old →
      ∀ (j1 : Nat), (hj1 : j1 < bands.length) →
        (bands[j1]'hj1).id = "" →
        bands.findIdx? (fun b_ => b_.id == old.fromId || decide (old.fromId ∈ b_.members)) = some j1 →
        bands.findIdx? (fun b_ => b_.id == old.toId || decide (old.toId ∈ b_.members)) = some j1 →
        ∀ (j : Nat), (hj : j < bands.length) → (bands[j]'hj).id ≠ "" →
          bands.findIdx? (fun b_ => b_.id == b_old.id || decide (b_old.id ∈ b_.members)) = some j →
          ∀ p ∈ old.points,
            axis.start b_old.rect + axis.length b_old.rect + (bands[j]'hj).shift ≤
              axis.point p + (bands[j1]'hj1).shift

 /-- Corrected consumer: the per-pair above-box bound implies the kept-route miss, by the one-sided strip argument. It replaces the deleted `pinLooseVictimMissOfLower` (false lower-bound premise) whenever the lane box end is at or below the loose slot start. -/
theorem pinLooseVictimMissOfAboveLane {axis : Axis}
    {r old : Route} {b b_old : Box} {shiftR shiftB : Int}
    (hrPts : r.points = old.points.map (lvShiftPoint axis shiftR))
    (hbRect : b.rect = lvShiftRect axis shiftB b_old.rect)
    (hweak : ∀ p ∈ old.points,
      axis.start b_old.rect + axis.length b_old.rect + shiftB ≤
        axis.point p + shiftR) :
    ¬ Polyline.hitsRect r.points b.rect := by
  have hroute : ∀ q ∈ r.points,
      axis.start b_old.rect + axis.length b_old.rect + shiftB ≤ axis.point q := by
    rw [hrPts]
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    rw [llLooseLower_shiftPoint_point]
    exact hweak p hp
  have hbox : axis.start b.rect + axis.length b.rect ≤
      axis.start b_old.rect + axis.length b_old.rect + shiftB := by
    rw [hbRect, llLooseLower_shiftRect_start, llLooseLower_shiftRect_length]
    omega
  exact llLooseLower_stripMiss hroute hbox

end LaneBands
end Layered
end Elegant
