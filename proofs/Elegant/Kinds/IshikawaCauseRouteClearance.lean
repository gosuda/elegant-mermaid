import Elegant.Kinds.IshikawaSameRibEnvelope
import Elegant.Kinds.IshikawaPlaceDrawnBound
import Elegant.IshikawaClearanceHard
import Elegant.IshikawaClearanceHardA
import Elegant.Kinds.IshikawaC6Facts
import ElegantGeometry.Route

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

def nsC : List Tree.Node :=
  [{ parent := none, width := 60, height := 30 },
   { parent := some 0, width := 60, height := 30 },
   { parent := some 1, width := 60, height := 30 },
   { parent := some 2, width := 60, height := 30 }]

def pC : Params := Elegant.Kinds.Ishikawa.params .vector

def ribsC : List Rib := (children nsC 0).zipIdx.map (generatedRib nsC)

def rC : Rib := effectivePlacedInput nsC (measuredSideLength pC ribsC) (generatedRib nsC (1, 0))

def spineC : Int := 32000

def e0C : Entry := ⟨2, -1, 2⟩

def e1C : Entry := ⟨3, 0, 3⟩

theorem entriesEqC : rC.entries = [e0C, e1C] := by rfl

theorem orderEqC : rC.order = [0, 1] := by rfl

theorem hpos1C : rC.order.zipIdx.find? (fun v => v.1 == 1) = some (1, 1) := by rfl

def nJC : Tree.Node := { parent := some 2, width := 60, height := 30 }

theorem hnJC : nsC[e1C.node]? = some nJC := by rfl

theorem he1C : (e1C, 1) ∈ rC.entries.zipIdx := by rw [entriesEqC]; simp

def marginC : Int := run pC rC.heights + 3

def rootC : Bone := { x1 := -run pC rC.length, t1 := rC.length, count := (children nsC rC.cause).length }

def t0C : Int := Int.fdiv (rC.length * (0 + 1 : Nat)) (rC.entries.length + 1 : Nat)

def parentEven0C : Bone := depthBone pC rootC 2 t0C (children nsC 2).length marginC

theorem hEntry0C : IndexedBoneGenealogy nsC pC rC 1 parentEven0C := by
  have hpar : IndexedBoneGenealogy nsC pC rC ((-1 + 1 : Int)).toNat rootC := by
    have h0 : ((-1 + 1 : Int)).toNat = 0 := by rfl
    rw [h0]
    exact .root
  have he : (e0C, 0) ∈ rC.entries.zipIdx := by rw [entriesEqC]; simp
  have hpos : rC.order.zipIdx.find? (fun v => v.1 == 0) = some (0, 0) := by rfl
  exact .entry rootC e0C 0 (0, 0) hpar he hpos

def parDC : Bone := { parentEven0C with drawn := 1 }

theorem hDraw1C : IndexedBoneGenealogy nsC pC rC 1 parDC := by
  have h := IndexedBoneGenealogy.draw (index := 1) (b := parentEven0C) hEntry0C
  have heq : ({ parentEven0C with drawn := parentEven0C.drawn + 1 } : Bone) = parDC := by rfl
  rw [heq] at h
  exact h

theorem hOwnerC : (e1C.parent + 1).toNat = 1 := by rfl

theorem hGeneJC : IndexedBoneGenealogy nsC pC rC (e1C.parent + 1).toNat parDC := by
  rw [hOwnerC]
  exact hDraw1C

def tJC : Int := Int.fdiv (rC.length * (1 + 1 : Nat)) (rC.entries.length + 1 : Nat)

def bJC : Bone := depthBone pC parDC e1C.depth tJC (children nsC e1C.node).length (run pC rC.heights + 3)

def routeCC : List Point := [⟨0, spineC⟩, ⟨-run pC rC.length, ordinate spineC rC.upper rC.length⟩]

def boxCC : Rect := ⟨bJC.x1 - nJC.width, ordinate spineC rC.upper bJC.t1 - Int.fdiv nJC.height 2, nJC.width, nJC.height⟩

theorem hitBCC : Polyline.hitsRectB routeCC boxCC = true := by rfl

theorem hitCC : Polyline.hitsRect routeCC boxCC :=
  (Polyline.hitsRectB_iff routeCC boxCC).mp hitBCC

theorem causeRouteEntryBoxCounterexample
    (raw : Tree.Layout) (_hrun : layout nsC pC = .ok raw)
    (_hg : ribsC = (children nsC 0).zipIdx.map (generatedRib nsC))
    (_hsource : generatedRib nsC (1, 0) ∈ ribsC)
    (_hcause : (1 : Nat) ∈ children nsC 0)
    (placed : Rib) (_hplace : place nsC pC spineC rC = .ok placed) :
    Polyline.hitsRect
      [⟨0, spineC⟩, ⟨-run pC rC.length, ordinate spineC rC.upper rC.length⟩]
      ⟨bJC.x1 - nJC.width, ordinate spineC rC.upper bJC.t1 - Int.fdiv nJC.height 2,
        nJC.width, nJC.height⟩ :=
  hitCC

theorem ishikawaCauseRouteEntryBoxClearance_false
    (raw : Tree.Layout) (_hrun : layout nsC pC = .ok raw)
    (_hg : ribsC = (children nsC 0).zipIdx.map (generatedRib nsC))
    (_hsource : generatedRib nsC (1, 0) ∈ ribsC)
    (_hcause : (1 : Nat) ∈ children nsC 0)
    (placed : Rib) (_hplace : place nsC pC spineC rC = .ok placed) :
    ¬ IshikawaCauseRouteEntryBoxClearance nsC pC raw _hrun ribsC _hg 1 0 _hsource _hcause spineC placed _hplace := by
  intro hDef
  have h := hDef e1C 1 (1, 1) parDC nJC he1C hpos1C hnJC hGeneJC
  exact absurd hitCC h

private theorem causeDiagonalMissExact
    (x0 x1 t0 t1 t width height reservation spine : Int) (up : Bool)
    (ht : t0 < t1) (hx : x1 ≤ x0) (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hcoverage : (x0 - x1) * height ≤ (t1 - t0) * reservation) :
    ¬ Polyline.hitsRect
      [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
      ⟨x0 + Int.fdiv ((x1 - x0) * (t - t0)) (t1 - t0) - reservation - width,
        ordinate spine up t - Int.fdiv height 2, width, height⟩ := by
  let span := t1 - t0
  let fall := x0 - x1
  let q := Int.fdiv ((x1 - x0) * (t - t0)) span
  have hspan : 0 < span := by dsimp only [span]; omega
  have hfall : 0 ≤ fall := by dsimp only [fall]; omega
  have hnormalX : x1 - x0 = -fall := by dsimp only [fall]; omega
  have hfloor : span * q ≤ -(fall * t) + fall * t0 := by
    have hq := Int.mul_fdiv_add_fmod ((x1 - x0) * (t - t0)) span
    have hr := Int.fmod_nonneg_of_pos ((x1 - x0) * (t - t0)) hspan
    have hraw : span * q ≤ (x1 - x0) * (t - t0) := by
      dsimp only [q]
      omega
    rw [hnormalX] at hraw
    simp only [Int.mul_sub, Int.neg_mul] at hraw
    omega
  have hhalf : 0 ≤ Int.fdiv height 2 ∧ Int.fdiv height 2 ≤ height := by
    rw [Tree.fdiv2]
    omega
  have hwidthProduct := Int.mul_nonneg (Int.le_of_lt hspan) hw
  have hhalfProduct := Int.mul_nonneg hfall hhalf.1
  have hremainingProduct := Int.mul_nonneg hfall
    (show 0 ≤ height - Int.fdiv height 2 by omega)
  simp only [Int.mul_sub] at hremainingProduct
  change fall * height ≤ span * reservation at hcoverage
  change ¬ Polyline.hitsRect
    [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
    ⟨x0 + q - reservation - width, ordinate spine up t - Int.fdiv height 2,
      width, height⟩
  have hneq : (⟨x0, ordinate spine up t0⟩ : Point) ≠
      ⟨x1, ordinate spine up t1⟩ := by
    intro heq
    have hy := congrArg Point.y heq
    cases up <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte] at hy <;> omega
  intro hhit
  apply hhit.2.2
  constructor
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    refine ⟨hneq, ?_⟩
    cases up with
    | false =>
      apply Or.inl
      have hnormalY : (spine + t0) - (spine + t1) = -span := by
        dsimp only [span]
        omega
      simp only [Polyline.minCorner, Int.le_min]
      constructor <;> constructor
      all_goals
        simp only [ordinate, Bool.false_eq_true, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
    | true =>
      apply Or.inr
      have hnormalY : (spine - t0) - (spine - t1) = span := by
        dsimp only [span]
        omega
      simp only [Polyline.maxCorner, Int.max_le]
      constructor <;> constructor
      all_goals
        simp only [ordinate, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
  · trivial

private theorem causeDiagonalMissOfEnv
    (x0 x1 t0 t1 t width height reservation spine : Int) (up : Bool)
    (boxX : Int)
    (ht : t0 < t1) (hx : x1 ≤ x0) (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hcoverage : (x0 - x1) * height ≤ (t1 - t0) * reservation)
    (hbox : boxX ≤ x0 + Int.fdiv ((x1 - x0) * (t - t0)) (t1 - t0) - reservation - width) :
    ¬ Polyline.hitsRect
      [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
      ⟨boxX, ordinate spine up t - Int.fdiv height 2, width, height⟩ := by
  let q := Int.fdiv ((x1 - x0) * (t - t0)) (t1 - t0)
  let reservation' := x0 + q - width - boxX
  have hboxEq : boxX = x0 + q - reservation' - width := by dsimp only [reservation']; omega
  have hresLe : reservation ≤ reservation' := by dsimp only [reservation']; omega
  have hspanPos : 0 < t1 - t0 := by omega
  have hcoverage' : (x0 - x1) * height ≤ (t1 - t0) * reservation' := by
    have h1 : (t1 - t0) * reservation ≤ (t1 - t0) * reservation' :=
      Int.mul_le_mul_of_nonneg_left hresLe (Int.le_of_lt hspanPos)
    omega
  rw [hboxEq]
  exact causeDiagonalMissExact x0 x1 t0 t1 t width height reservation' spine up ht hx hw hh hcoverage'

def IshikawaCauseRouteEntryBoxClearanceAccounted (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
  ∀ (eJ : Entry) (idxJ : Nat) (posJ : Nat × Nat) (parJ : Bone) (nJ : Tree.Node),
    (eJ, idxJ) ∈ r.entries.zipIdx →
    r.order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ →
    ns[eJ.node]? = some nJ →
    IndexedBoneGenealogy ns p r (eJ.parent + 1).toNat parJ →
    let tJ := Int.fdiv (r.length * (posJ.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bJ := depthBone p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3)
    bJ.x1 ≤ envMasterX r p bJ.t1 - (run p r.heights + 1) →
    ¬ Polyline.hitsRect
      [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]
      ⟨bJ.x1 - nJ.width, ordinate spine r.upper bJ.t1 - Int.fdiv nJ.height 2,
        nJ.width, nJ.height⟩

theorem ishikawaCauseRouteEntryBoxClearanceAccounted
    (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) :
    IshikawaCauseRouteEntryBoxClearanceAccounted ns p raw _hrun ribs _hg cause k _hsource _hcause spine placed _hplace := by
  unfold IshikawaCauseRouteEntryBoxClearanceAccounted
  intro r eJ idxJ posJ parJ nJ heJ hposJ hnJ hgeneJ tJ bJ hENV
  have hne : ns ≠ [] := by
    intro hnil
    simp [hnil, children] at _hcause
  obtain ⟨hcos, hsin1, _hinset, _hstub, _hbase, _hper, _hspineBase, _hribMin⟩ :=
    Elegant.Kinds.IshikawaC6Facts.layout_parameters_sane ns p raw hne _hrun
  have hsin : 0 < p.sin := by omega
  have hdims := successful_node_dimensions ns p raw _hrun nJ (List.mem_of_getElem? hnJ)
  have hbound : nJ.height ≤ r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    measured_entry_height_bound ns r.entries eJ (List.fst_mem_of_mem_zipIdx heJ) nJ hnJ
  have hfields : (generatedRib ns (cause, k)).heights =
      (generatedRib ns (cause, k)).entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    (generated_rib_fields ns cause k).2.2.2
  have hentriesEq : r.entries = (generatedRib ns (cause, k)).entries := by rfl
  have hheightsEq : r.heights = (generatedRib ns (cause, k)).heights := by rfl
  have hbudget0 := generated_reservation_budget ns p ribs _hg (generatedRib ns (cause, k)) _hsource
    (by
      cases h : (generatedRib ns (cause, k)).entries with
      | nil =>
        have he0 : eJ ∈ (generatedRib ns (cause, k)).entries := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp (hentriesEq ▸ heJ))
        rw [h] at he0
        exact absurd he0 (by simp)
      | cons _ _ => rfl)
  have hbudget : (r.entries.length + 1 : Nat) * r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length := by
    have h1 : ((generatedRib ns (cause, k)).entries.length + 1 : Nat) * (generatedRib ns (cause, k)).heights ≤
        (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).length := hbudget0
    rw [hfields] at h1
    have heq1 : r.entries.length = (generatedRib ns (cause, k)).entries.length := by rw [hentriesEq]
    have heq2 : r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 =
        (generatedRib ns (cause, k)).entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by rw [hentriesEq]
    have heq3 : r.length = (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).length := rfl
    rw [heq1, heq2, heq3]
    exact h1
  have hmaxH : 0 ≤ r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    entry_height_fold_initial ns _ 0
  have hHle : nJ.height ≤ r.heights := by
    have h1 : r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 = r.heights := by
      rw [hheightsEq, hfields, hentriesEq]
    rw [h1] at hbound
    exact hbound
  have hHnn : 0 ≤ r.heights := Int.le_trans hmaxH (by rw [hheightsEq, hfields, hentriesEq]; exact Int.le_refl _)
  have hLnn : 0 ≤ r.length := by
    have hpos : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int) := by omega
    have hmul := Int.mul_nonneg hpos hmaxH
    omega
  have hRunL : 0 ≤ run p r.length := Elegant.Kinds.IshikawaC6Facts.run_nonneg p r.length hcos (by omega) hLnn
  have hRunH : 0 ≤ run p r.heights := Elegant.Kinds.IshikawaC6Facts.run_nonneg p r.heights hcos (by omega) hHnn
  have hFoldEq : r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 = r.heights := by
    rw [hheightsEq, hfields, hentriesEq]
  have hFoldPos : 0 < r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
    rw [hFoldEq]
    have h1 : (1 : Int) ≤ nJ.height := by omega
    omega
  have hLenPos : 0 < ((r.entries.length + 1 : Nat) : Int) := by omega
  have hProdPos : 0 < ((r.entries.length + 1 : Nat) : Int) * r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    Int.mul_pos hLenPos hFoldPos
  have hPos : 0 < r.length := Int.lt_of_lt_of_le hProdPos hbudget
  have hbJt : bJ.t1 = tJ := by
    by_cases heven : eJ.depth % 2 = 0
    · have h := depthBone_even_endpoints p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3) heven
      simpa [bJ] using h.2.1
    · have hne : eJ.depth % 2 ≠ 0 := heven
      have h := depthBone_odd_endpoints p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3) hne
      simpa [bJ] using h.2.1
  have hMaster : envMasterX r p bJ.t1 = Int.fdiv ((-run p r.length) * tJ) r.length := by
    rw [hbJt]
    rfl
  have hbox : bJ.x1 - nJ.width ≤ 0 + Int.fdiv (((-run p r.length) - 0) * (tJ - 0)) (r.length - 0) - (run p r.heights + 1) - nJ.width := by
    have h1 : bJ.x1 ≤ envMasterX r p bJ.t1 - (run p r.heights + 1) := hENV
    rw [hMaster] at h1
    have hfdivEq : Int.fdiv ((-run p r.length) * tJ) r.length = Int.fdiv (((-run p r.length) - 0) * (tJ - 0)) (r.length - 0) := by simp
    rw [hfdivEq] at h1
    have heq3 : (0 : Int) + Int.fdiv (((-run p r.length) - 0) * (tJ - 0)) (r.length - 0) = Int.fdiv (((-run p r.length) - 0) * (tJ - 0)) (r.length - 0) := by simp
    omega
  have hcov0 : r.heights * run p r.length ≤ r.length * (run p r.heights + 1) :=
    run_scaled_cross_bound p r.heights r.length hHnn hLnn hsin
  have hcov1 : nJ.height * run p r.length ≤ r.length * (run p r.heights + 1) := by
    have hle : run p r.length * nJ.height ≤ run p r.length * r.heights :=
      Int.mul_le_mul_of_nonneg_left hHle hRunL
    have hcov0' : run p r.length * r.heights ≤ r.length * (run p r.heights + 1) := by
      have h := hcov0
      rwa [Int.mul_comm r.heights (run p r.length)] at h
    calc nJ.height * run p r.length = run p r.length * nJ.height := Int.mul_comm _ _
      _ ≤ run p r.length * r.heights := hle
      _ ≤ r.length * (run p r.heights + 1) := hcov0'
  have hcoverage : (0 - -run p r.length) * nJ.height ≤ (r.length - 0) * (run p r.heights + 1) := by
    have e1 : (0 - -run p r.length) = run p r.length := by simp
    have e2 : (r.length - 0) = r.length := by simp
    rw [e1, e2, Int.mul_comm (run p r.length) nJ.height]
    exact hcov1
  have ht : (0 : Int) < r.length := hPos
  have hx : -run p r.length ≤ 0 := by omega
  have hw : 0 ≤ nJ.width := by omega
  have hh : 0 ≤ nJ.height := by omega
  have hmiss := causeDiagonalMissOfEnv 0 (-run p r.length) 0 r.length tJ nJ.width nJ.height (run p r.heights + 1) spine r.upper (bJ.x1 - nJ.width) ht hx hw hh hcoverage hbox
  have hroute : ([⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩] : List Point) =
      [⟨0, ordinate spine r.upper 0⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩] := by
    cases r.upper <;> simp [ordinate]
  have hgoalBox : (⟨bJ.x1 - nJ.width, ordinate spine r.upper bJ.t1 - Int.fdiv nJ.height 2, nJ.width, nJ.height⟩ : Rect) =
      ⟨bJ.x1 - nJ.width, ordinate spine r.upper tJ - Int.fdiv nJ.height 2, nJ.width, nJ.height⟩ := by rw [hbJt]
  rw [hroute, hgoalBox]
  exact hmiss

end Elegant.Kinds.IshikawaFinal
