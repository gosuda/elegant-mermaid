import Elegant.IshikawaClearanceFacts
import Elegant.IshikawaAssemblyBoxFacts
import Elegant.Kinds.IshikawaSeparationFacts
import Elegant.Kinds.IshikawaOrthogonalityFacts
import Elegant.Kinds.IshikawaValid

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaC6Facts

open Elegant.Ishikawa

/-- Rib-local foreign clearance: inside one successfully placed rib, the route of
every piece misses the box of every other piece. This is the per-rib fact the
assembly transport reduces C6 to. -/
def RibLocalForeignClearance (placed : Rib) : Prop :=
  ∀ (i : Nat) (rectI : Rect) (pointsI : List Point),
    (i, rectI, pointsI) ∈ placed.pieces →
    ∀ (j : Nat) (rectJ : Rect) (pointsJ : List Point),
      (j, rectJ, pointsJ) ∈ placed.pieces → i ≠ j →
        ¬ Polyline.hitsRect pointsI ⟨rectJ.x, rectJ.y, rectJ.w, rectJ.h⟩

/-- `placed` is the rib list the actual layout pipeline produces: generated
ribs measured, placed by `place`, then assembled into `raw`. -/
def IsPlacedRibList (ns : List Tree.Node) (p : Params) (placed : List Rib)
    (raw : Tree.Layout) : Prop :=
  ∃ (ribs : List Rib) (length : Bool → Int) (spine : Int) (head : Tree.Node),
    ribs = (children ns 0).zipIdx.map (generatedRib ns) ∧
    length = measuredSideLength p ribs ∧
    spine = max (length true) p.spineBase ∧
    ribs.mapM (fun r => place ns p spine (effectivePlacedInput ns length r)) =
      .ok placed ∧
    ns[0]? = some head ∧
    layout ns p = .ok raw ∧
    assemblePairs spine placed (-p.inset) 0
      ⟨(List.replicate ns.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
        ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩,
        List.replicate ns.length []⟩ = .ok raw

/-- The rib-local clearance hypothesis: every rib the actual layout places
satisfies `RibLocalForeignClearance`. -/
def RibLocalClearanceHyp : Prop :=
  ∀ (ns : List Tree.Node) (p : Params) (placed : List Rib) (raw : Tree.Layout),
    IsPlacedRibList ns p placed raw →
    ∀ rib ∈ placed, RibLocalForeignClearance rib

private theorem placed_rib_place_source {ns : List Tree.Node} {p : Params}
    {placed : List Rib} {raw : Tree.Layout}
    (hpl : IsPlacedRibList ns p placed raw)
    {rib : Rib} (hrib : rib ∈ placed) :
    ∃ (ribs : List Rib) (length : Bool → Int) (spine : Int) (source : Rib)
      (_hsource : source ∈ ribs),
      ribs = (children ns 0).zipIdx.map (generatedRib ns) ∧
      length = measuredSideLength p ribs ∧
      spine = max (length true) p.spineBase ∧
      place ns p spine (effectivePlacedInput ns length source) = .ok rib ∧
      layout ns p = .ok raw := by
  obtain ⟨ribs, length, spine, head, hg, hlength, hspine, hplaces, hhead,
    hlayout, hassemble⟩ := hpl
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrib
  obtain ⟨source, hsource, hplace⟩ :=
    (Elegant.Kinds.Gitgraph.mapM_index_record _ _ _ hplaces).2 k rib hk
  exact ⟨ribs, length, spine, source, List.mem_of_getElem? hsource,
    hg, hlength, hspine, hplace, hlayout⟩

private theorem getElem?_map_eq {α β : Type} (f : α → β) (l : List α)
    (k : Nat) (v : β) (h : (l.map f)[k]? = some v) :
    ∃ u, l[k]? = some u ∧ f u = v := by
  rw [List.getElem?_map] at h
  cases hl : l[k]? with
  | none => simp [hl] at h
  | some u =>
    simp only [hl, Option.map_some] at h
    exact ⟨u, rfl, Option.some.inj h⟩

/-- Runtime facts for one placed rib of a successful layout: the effective input,
its place success, and the reservation budget used by clearance lemmas. -/
private theorem placed_rib_runtime {ns : List Tree.Node} {p : Params}
    {placed : List Rib} {raw : Tree.Layout}
    (hpl : IsPlacedRibList ns p placed raw)
    {rib : Rib} (hrib : rib ∈ placed) :
    ∃ (ribs : List Rib) (length : Bool → Int) (spine : Int) (source : Rib),
      ribs = (children ns 0).zipIdx.map (generatedRib ns) ∧
      length = measuredSideLength p ribs ∧
      spine = max (length true) p.spineBase ∧
      place ns p spine (effectivePlacedInput ns length source) = .ok rib ∧
      layout ns p = .ok raw ∧
      0 ≤ (effectivePlacedInput ns length source).length ∧
      ((effectivePlacedInput ns length source).entries.length + 1 : Nat) *
        (effectivePlacedInput ns length source).entries.foldl
          (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤
        (effectivePlacedInput ns length source).length := by
  obtain ⟨ribs, length, spine, source, hsource, hg, hlength, hspine, hplace,
    hlayout⟩ := placed_rib_place_source hpl hrib
  have hne : ns ≠ [] := by
    intro hnil
    rw [hnil] at hpl
    obtain ⟨ribs', length', spine', head', hg', hlength', hspine', hplaces',
      hhead', hlayout', hassemble'⟩ := hpl
    simp only [List.getElem?_nil] at hhead'
    cases hhead'
  obtain ⟨hmin, hbase⟩ := successful_nonempty_length_parameters ns p raw hne hlayout
  have hlen_nonneg : ∀ up : Bool, 0 ≤ length up := by
    intro up
    rw [hlength]
    unfold measuredSideLength
    dsimp only
    split
    · exact Int.le_trans (Int.le_trans (by omega : (0 : Int) ≤ p.ribMin)
        (Int.le_max_left _ _)) (rib_length_fold_initial _ _ _)
    · exact Int.le_trans (by omega : (0 : Int) ≤ p.spineBase)
        (rib_length_fold_initial _ _ _)
  have hinput_len : 0 ≤ (effectivePlacedInput ns length source).length := by
    simp only [effectivePlacedInput]
    by_cases hch : (children ns source.cause).isEmpty = true
    · simp only [hch, ↓reduceIte]
      exact Int.fdiv_nonneg (hlen_nonneg source.upper) (by decide)
    · simp only [hch, Bool.false_eq_true, ↓reduceIte]
      exact hlen_nonneg source.upper
  have hheights : source.heights =
      source.entries.foldl (fun h e =>
        max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
    obtain ⟨cause, k, _, hgen⟩ :=
      generated_rib_source ns ribs hg source hsource
    rw [hgen]
    exact (generated_rib_fields ns cause k).2.2.2
  have hbudget0 : (source.entries.length + 1 : Nat) * source.heights ≤
      (effectivePlacedInput ns length source).length := by
    by_cases hneE : source.entries.isEmpty = false
    · rw [hlength]
      exact generated_reservation_budget ns p ribs hg source hsource hneE
    · have hentries : source.entries = [] := List.isEmpty_iff.mp (by
        cases h : source.entries.isEmpty with
        | false => exact absurd h hneE
        | true => rfl)
      have hfold : source.heights = 0 := by
        rw [hheights, hentries]
        rfl
      rw [hfold, hentries]
      simp
      exact hinput_len
  have hbudget : ((effectivePlacedInput ns length source).entries.length + 1 : Nat) *
      (effectivePlacedInput ns length source).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤
      (effectivePlacedInput ns length source).length := by
    have he : (effectivePlacedInput ns length source).entries = source.entries := rfl
    have hh : (effectivePlacedInput ns length source).heights = source.heights := rfl
    rw [he, ← hheights]
    exact hbudget0
  exact ⟨ribs, length, spine, source, hg, hlength, hspine, hplace, hlayout,
    hinput_len, hbudget⟩

/-! ### Layout parameter sanity -/

theorem layout_parameters_sane (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hne : ns ≠ []) (hrun : layout ns p = .ok raw) :
    0 ≤ p.cos ∧ 1 ≤ p.sin ∧ 0 ≤ p.inset ∧ 1 ≤ p.stub ∧ 1 ≤ p.base ∧
      0 ≤ p.perChild ∧ 0 ≤ p.spineBase ∧ 0 ≤ p.ribMin := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons head rest =>
    unfold layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun
      cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun
        cases hrun
      · rename_i hparameters
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hparameters
        omega

theorem run_nonneg (p : Params) (rise : Int) (hcos : 0 ≤ p.cos) (hsin : 1 ≤ p.sin)
    (h : 0 ≤ rise) : 0 ≤ run p rise :=
  Int.fdiv_nonneg (Int.mul_nonneg h hcos) (by omega)

private theorem fdiv_nonpos_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : 0 < b) :
    Int.fdiv a b ≤ 0 := by
  have hkey := Int.mul_fdiv_add_fmod a b
  have hmodpos := Int.fmod_nonneg_of_pos a hb
  by_cases hle : Int.fdiv a b ≤ 0
  · exact hle
  · have hge : 1 ≤ Int.fdiv a b := by omega
    have hmul : b * 1 ≤ b * Int.fdiv a b :=
      Int.mul_le_mul_of_nonneg_left hge (Int.le_of_lt hb)
    have hle1 : b ≤ b * Int.fdiv a b := by simpa using hmul
    omega

/-! ### Assembly transport for foreign route/box clearance -/

/-- Same-level cross-rib clearance: ribs of opposite sides (as adjacent generated ribs
are) have piece routes that miss each other's piece boxes. -/
def CrossRibClearance (rs : List Rib) : Prop :=
  ∀ a ∈ rs, ∀ b ∈ rs, a ≠ b → a.upper ≠ b.upper →
    ∀ pa ∈ a.pieces, ∀ pb ∈ b.pieces,
      ¬ Polyline.hitsRect pa.2.2 ⟨pb.2.1.x, pb.2.1.y, pb.2.1.w, pb.2.1.h⟩

/-- Consecutive ribs of the list alternate between the upper and lower side. -/
def AdjacentAlternate (rs : List Rib) : Prop :=
  ∀ u v : Rib, ∀ pre post : List Rib, rs = pre ++ u :: v :: post → u.upper ≠ v.upper

theorem adjacentAlternate_tail {a : Rib} {rest : List Rib}
    (h : AdjacentAlternate (a :: rest)) : AdjacentAlternate (rest.drop 1) := by
  intro u v pre' post' hsuf'
  refine h u v ((a :: rest.take 1) ++ pre') post' ?_
  have hsplit : a :: rest = (a :: rest.take 1) ++ rest.drop 1 := by
    cases rest with
    | nil => rfl
    | cons x xs => rfl
  rw [hsplit, List.append_assoc, hsuf']

private theorem bindE_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x >>= f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

end Elegant.Kinds.IshikawaC6Facts
