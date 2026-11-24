import Elegant.Kinds.IshikawaSameRibFramesProof
import Elegant.Kinds.IshikawaCauseRouteClearance

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant
open Elegant.Ishikawa

/-! ### Cause entry envelope bound over executed frames

Every entry bone of the executed birth frames ends (`x1`) at or left of the
cause line's master diagonal at its own `t1`, minus `run p r.heights + 1`.

Route: induction over entry depth (`key`), following the exact case split of
`Elegant.Ishikawa.ishikawa_env_invariant`. A root child (depth 2) attaches to
the rib root by exact even-birth interpolation, then runs left by `boneLength`
(which covers the reservation). A non-root even child interpolates its odd
parent's span and runs left; a non-root odd child starts at an interpolated
point of its even parent's span with the attachment start margin and falls
along the slope. The one-step arithmetic is the already-proved
`env_step_odd_slack` / `env_step_even_slack`; the two private floor-alignment
facts they need are copied below under new names. -/

/-- Copied from `IshikawaClearanceHardA.fdiv_bounds` (private there). -/
private theorem causeEnv_fdiv_bounds (a d : Int) (hd : 0 < d) :
    d * Int.fdiv a d ≤ a ∧ a < d * Int.fdiv a d + d := by
  have h := Int.mul_fdiv_add_fmod a d
  have hf := Int.fmod_nonneg_of_pos a hd
  have hlt := Int.fmod_lt_of_pos a hd
  omega

/-- Copied from `IshikawaClearanceHardA.slot_strict` (private there): entry
slots are strictly increasing in the entry position. -/
private theorem causeEnv_slot_strict (L d : Int) (hL : 0 < L) (hd : 0 < d) (hLd : d ≤ L)
    (a c : Nat) (hac : a < c) :
    Int.fdiv (L * (a + 1 : Nat)) d < Int.fdiv (L * (c + 1 : Nat)) d := by
  have hstep : Int.fdiv (L * (a + 1 : Nat)) d + 1 ≤ Int.fdiv (L * (a + 1 : Nat) + d) d := by
    have h1 := causeEnv_fdiv_bounds (L * (a + 1 : Nat)) d hd
    have h2 := causeEnv_fdiv_bounds (L * (a + 1 : Nat) + d) d hd
    have hlt : d * Int.fdiv (L * (a + 1 : Nat)) d <
        d * Int.fdiv (L * (a + 1 : Nat) + d) d := by omega
    exact Int.lt_of_mul_lt_mul_left hlt (by omega)
  have hmono : Int.fdiv (L * (a + 1 : Nat) + d) d ≤ Int.fdiv (L * (c + 1 : Nat)) d := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ d by omega),
      Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ d by omega)]
    refine Int.ediv_le_ediv (by omega) ?_
    have h1 : L * ↑(a + 1) + d ≤ L * ↑(a + 1) + L := by omega
    have h2 : L * ↑(a + 1) + L = L * ↑(a + 1) + L * 1 := by
      rw [Int.mul_one]
    have h3 : L * ↑(a + 1) + L * 1 = L * (↑(a + 1) + 1) := by
      rw [← Int.mul_add]
    have h4 : L * (↑(a + 1) + 1) ≤ L * ↑(c + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hL)
    omega
  omega

/-- Copied from `IshikawaClearanceHardA.depthBone_even_congr'` (private
there): the even branch ignores the parity selector and the `drawn` field. -/
private theorem causeEnv_depthBone_even_congr' (p : Params) (par : Bone) (δ : Int) (d d' : Nat)
    (t count margin : Int) (hd : d % 2 = 0) (hd' : d' % 2 = 0) :
    depthBone p { par with drawn := δ } d t count margin = depthBone p par d' t count margin := by
  have h1 : ((d : Nat) % 2 != 0) = false := by rw [hd]; decide
  have h2 : ((d' : Nat) % 2 != 0) = false := by rw [hd']; decide
  simp only [depthBone, h1, h2, Bool.false_eq_true, ite_false]

/-- Copied from `IshikawaClearanceHardA.depthBone_odd_congr` (private there):
any two odd depths give the same bone. -/
private theorem causeEnv_depthBone_odd_congr (p : Params) (par : Bone) (d d' : Nat) (t count margin : Int)
    (hd : d % 2 ≠ 0) (hd' : d' % 2 ≠ 0) :
    depthBone p par d t count margin = depthBone p par d' t count margin := by
  have hm : d % 2 = 1 := by omega
  have hm' : d' % 2 = 1 := by omega
  simp only [depthBone, show ((d : Nat) % 2 != 0) = true from by rw [hm]; decide,
    show ((d' : Nat) % 2 != 0) = true from by rw [hm']; decide, ite_true]

/-- Frames-only ENV residual for the cause case: every entry bone of the
executed birth frames ends at or left of the master diagonal at its own `t1`,
minus `run p r.heights + 1`. Probed over all link-valid trees to seven nodes
in both profiles (`IshikawaCauseEnvProbe`): 650 envelope pairs, 0 violations,
minimum gap 2 (cell) / 1018 (vector). -/
theorem causeEntryEnvBound (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed) :
    CauseEntryEnvBound ns p raw hrun ribs hg cause k hsource hcause spine placed hplace := by
  intro frames e idx b hlength hrootFrame hrecords hframe hmem
  obtain ⟨r, hrdef⟩ : ∃ r, r = effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k)) := ⟨_, rfl⟩
  rw [← hrdef] at hplace hlength hrootFrame hrecords hmem ⊢
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hcauseLt : cause < ns.length := List.mem_range.mp (List.mem_filter.mp hcause).1
  have hne : ns ≠ [] := by
    intro hnil
    rw [hnil] at hcauseLt
    exact Nat.not_lt_zero _ hcauseLt
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hcos : 0 ≤ p.cos := hparameters.1
  have hsin : 0 < p.sin := Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hparameters.2
  have hentriesEq : r.entries = (generatedRib ns (cause, k)).entries := by rw [hrdef]; rfl
  have src_mem : ∀ (e : Entry) (i : Nat),
      (e, i) ∈ r.entries.zipIdx → (e, i) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    fun e i h => hentriesEq ▸ h
  have slotMono : ∀ (a c : Nat), a ≤ c → 0 ≤ r.length →
      Int.fdiv (r.length * (a + 1 : Nat)) (r.entries.length + 1 : Nat) ≤
        Int.fdiv (r.length * (c + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    intro a c hac hlen
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega : 0 ≤ ((r.entries.length + 1 : Nat) : Int)),
      Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    refine Int.ediv_le_ediv (by omega) ?_
    exact Int.mul_le_mul_of_nonneg_left (by omega) hlen
  have key : ∀ (d : Nat) (e : Entry) (idx : Nat) (b : Bone),
      (e, idx) ∈ r.entries.zipIdx → e.depth = d → idx < r.entries.length →
      frames[idx + 1]? = some b →
      ParentBoneSlack r p b ∧
      b.x1 ≤ envMasterX r p b.t1 - (run p r.heights + 1) := by
    intro d
    induction d with
    | zero =>
      intro e idx b hmem hdepth hlt hframe
      by_cases hroot : e.parent = -1
      · have hd2 := generated_root_depth ns cause k hlink hcause e idx
          (src_mem e idx hmem) hroot
        omega
      · obtain ⟨doneE, restE, hprefixE, _⟩ := List.eq_append_cons_of_mem hmem
        obtain ⟨_, _, _, _, hparentFrame, _, _⟩ :=
          hrecords doneE e idx restE hprefixE
        have hownerLt : (e.parent + 1).toNat < frames.length :=
          (List.getElem?_eq_some_iff.mp hparentFrame).1
        have hlb := generated_entry_parent_lower_bound ns cause k e idx (src_mem e idx hmem)
        have hge : 0 ≤ e.parent := by omega
        have hownEq : (e.parent + 1).toNat = e.parent.toNat + 1 := by
          omega
        have hparentLt : e.parent.toNat < r.entries.length := by omega
        have heP : (r.entries[e.parent.toNat]'hparentLt, e.parent.toNat) ∈ r.entries.zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hparentLt)
        have hd := generated_parent_child_depth ns cause k hlink hcause
          (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
          (src_mem _ _ heP) (src_mem e idx hmem) (by rw [Int.toNat_of_nonneg hge])
        omega
    | succ d ihd =>
      intro e idx b hmem hdepth hlt hframe
      obtain ⟨doneE, restE, hprefixE, _⟩ := List.eq_append_cons_of_mem hmem
      obtain ⟨pos, parentFrame, born, hpos, hparentFrame, hbornLookup, hborn⟩ :=
        hrecords doneE e idx restE hprefixE
      have hbf : b = born := Option.some.inj (hframe.symm.trans hbornLookup)
      obtain ⟨slot, hslot⟩ : ∃ slot : Int,
          slot = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
        ⟨_, rfl⟩
      rw [← hslot] at hborn
      have hownerLt : (e.parent + 1).toNat < frames.length :=
        (List.getElem?_eq_some_iff.mp hparentFrame).1
      have hmemSrc : e ∈ (generatedRib ns (cause, k)).entries :=
        List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp (src_mem e idx hmem))
      by_cases hroot : e.parent = -1
      · -- root child: depth 2, parent frame is the rib root
        have hnodeMem : e.node ∈ children ns cause :=
          generated_root_child_membership ns cause k e idx (src_mem e idx hmem) hroot
        have hnodeLt : e.node < ns.length := List.mem_range.mp (List.mem_filter.mp hnodeMem).1
        have hn : ns[e.node]? = some (ns[e.node]'hnodeLt) := List.getElem?_eq_getElem hnodeLt
        have hdims := successful_node_dimensions ns p raw hrun (ns[e.node]'hnodeLt)
          (List.mem_of_getElem? hn)
        have hheightsEq : r.heights = (generatedRib ns (cause, k)).heights := by
          rw [hrdef]; rfl
        have hheights : 1 ≤ r.heights := by
          rw [hheightsEq, (generated_rib_fields ns cause k).2.2.2]
          have hm := measured_entry_height_bound ns (generatedRib ns (cause, k)).entries e
            hmemSrc (ns[e.node]'hnodeLt) hn
          omega
        have hneEntries : (generatedRib ns (cause, k)).entries.isEmpty = false := by
          cases hentries : (generatedRib ns (cause, k)).entries with
          | nil => rw [hentries] at hmemSrc; exact absurd hmemSrc (by simp)
          | cons child rest => rfl
        have hbudget := generated_reservation_budget ns p ribs hg
          (generatedRib ns (cause, k)) hsource hneEntries
        have hLd : ((r.entries.length + 1 : Nat) : Int) ≤ r.length := by
          have hc : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int) := by omega
          have hmul := Int.mul_le_mul_of_nonneg_left hheights hc
          have h1 : ((r.entries.length + 1 : Nat) : Int) * r.heights ≤ r.length := by
            rw [hentriesEq, hheightsEq, hrdef]
            exact hbudget
          omega
        have hrlen : 0 < r.length := by omega
        have hd2 := generated_root_depth ns cause k hlink hcause e idx
          (src_mem e idx hmem) hroot
        rw [hd2] at hborn
        have hzero : (e.parent + 1).toNat = 0 := by rw [hroot]; rfl
        rw [hzero] at hparentFrame
        have hrootEq : parentFrame =
            ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) :=
          Option.some.inj (hparentFrame.symm.trans hrootFrame)
        have h2n : ((2 : Nat) % 2 != 0) = false := by decide
        have hshape := depthBone_even_endpoints p
          { parentFrame with drawn := processedOddDraws doneE ((e.parent + 1).toNat) } 2 slot
          (children ns e.node).length (run p r.heights + 3) (by decide : (2 : Nat) % 2 = 0)
        rw [← hborn] at hshape
        have hmargin : 0 ≤ run p r.heights :=
          Int.fdiv_nonneg (Int.mul_nonneg (by omega : 0 ≤ r.heights) hcos) (Int.le_of_lt hsin)
        have hbl := boneLength_margin p (children ns e.node).length (run p r.heights + 3)
          (by omega)
        have hbx0 : born.x0 = envMasterX r p slot := by
          rw [hborn, hrootEq]
          simp only [depthBone, h2n, Bool.false_eq_true, ite_false, Int.sub_zero,
            Int.zero_add, envMasterX]
        rw [hbf]
        have hslotNN : 0 ≤ slot := by
          rw [hslot]
          exact Int.fdiv_nonneg
            (Int.mul_nonneg (Int.le_of_lt hrlen)
              (by omega : (0 : Int) ≤ ((pos.2 + 1 : Nat) : Int)))
            (by omega : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int))
        have hbc : born.count = ((children ns e.node).length : Int) := by
          rw [hborn, hrootEq]
          simp only [depthBone, h2n, Bool.false_eq_true, ite_false]
        have hbl2 : (((children ns e.node).length : Int) + 1) * (run p r.heights + 3)
            ≤ boneLength p (children ns e.node).length (run p r.heights + 3) :=
          Int.le_max_right _ _
        refine ⟨?_, by rw [hshape.2.1, hshape.2.2, hbx0]; omega⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hshape.1]; exact hslotNN
        · exact Int.le_of_eq (hshape.1.trans hshape.2.1.symm)
        · rw [hshape.1, hbx0]; exact Int.le_of_eq rfl
        · intro hdeg
          rw [hshape.1, hshape.2.1] at hdeg
          rw [hbc, hshape.2.2]; omega
        · intro habs
          rw [hshape.1, hshape.2.1] at habs
          exact absurd habs (by omega)
      · -- non-root child
        have hlb := generated_entry_parent_lower_bound ns cause k e idx (src_mem e idx hmem)
        have hge : 0 ≤ e.parent := by omega
        have hownEq : (e.parent + 1).toNat = e.parent.toNat + 1 := by
          omega
        have hparEq : e.parent = (e.parent.toNat : Int) := (Int.toNat_of_nonneg hge).symm
        have hparentLt : e.parent.toNat < r.entries.length := by omega
        have hparentLookup : r.entries[e.parent.toNat]? =
            some (r.entries[e.parent.toNat]'hparentLt) := List.getElem?_eq_getElem hparentLt
        have heP : (r.entries[e.parent.toNat]'hparentLt, e.parent.toNat) ∈ r.entries.zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr hparentLookup
        obtain ⟨doneP, restP, hprefixP, _⟩ := List.eq_append_cons_of_mem heP
        obtain ⟨posP, grandFrame, parentBorn, hposP, hgrandFrame, hparentBornLookup, hparentBorn⟩ :=
          hrecords doneP (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat restP hprefixP
        rw [hownEq] at hparentFrame
        have hPB : parentBorn = parentFrame :=
          Option.some.inj (hparentBornLookup.symm.trans hparentFrame)
        have hd := generated_parent_child_depth ns cause k hlink hcause
          (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
          (src_mem _ _ heP) (src_mem e idx hmem) hparEq
        have hdepthPar : (r.entries[e.parent.toNat]'hparentLt).depth = d := by omega
        have ihP := ihd (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat parentBorn heP
          hdepthPar hparentLt hparentBornLookup
        rw [hPB] at ihP
        have hnodeMem : e.node ∈ children ns (r.entries[e.parent.toNat]'hparentLt).node :=
          generated_parent_child_membership ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
            (src_mem _ _ heP) (src_mem e idx hmem) hparEq
        have hnodeLt : e.node < ns.length := List.mem_range.mp (List.mem_filter.mp hnodeMem).1
        have hn : ns[e.node]? = some (ns[e.node]'hnodeLt) := List.getElem?_eq_getElem hnodeLt
        have hdims := successful_node_dimensions ns p raw hrun (ns[e.node]'hnodeLt)
          (List.mem_of_getElem? hn)
        have hheightsEq : r.heights = (generatedRib ns (cause, k)).heights := by rw [hrdef]; rfl
        have hheights : 1 ≤ r.heights := by
          rw [hheightsEq, (generated_rib_fields ns cause k).2.2.2]
          have hm := measured_entry_height_bound ns (generatedRib ns (cause, k)).entries e
            hmemSrc (ns[e.node]'hnodeLt) hn
          omega
        have hneEntries : (generatedRib ns (cause, k)).entries.isEmpty = false := by
          cases hentries : (generatedRib ns (cause, k)).entries with
          | nil => rw [hentries] at hmemSrc; exact absurd hmemSrc (by simp)
          | cons child rest => rfl
        have hbudget := generated_reservation_budget ns p ribs hg
          (generatedRib ns (cause, k)) hsource hneEntries
        have hLd : ((r.entries.length + 1 : Nat) : Int) ≤ r.length := by
          have hc : (0 : Int) ≤ ((r.entries.length + 1 : Nat) : Int) := by omega
          have hmul := Int.mul_le_mul_of_nonneg_left hheights hc
          have h1 : ((r.entries.length + 1 : Nat) : Int) * r.heights ≤ r.length := by
            rw [hentriesEq, hheightsEq, hrdef]
            exact hbudget
          omega
        have hrlen : 0 < r.length := by omega
        have hslotLen : slot ≤ r.length := by
          have hmemO := List.mem_of_find?_eq_some hpos
          have hgetO := List.mem_zipIdx_iff_getElem?.mp hmemO
          have hposLt : pos.2 < r.order.length := (List.getElem?_eq_some_iff.mp hgetO).1
          have hordLe : r.order.length ≤ r.entries.length := by
            rw [hrdef]
            exact Elegant.Kinds.IshikawaSeparation.generated_effective_order_length_le ns
              (measuredSideLength p ribs) cause k
          calc slot = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
              hslot
            _ ≤ Int.fdiv (r.length * (r.entries.length + 1 : Nat))
                (r.entries.length + 1 : Nat) := slotMono _ _ (by omega) (Int.le_of_lt hrlen)
            _ = r.length := Int.mul_fdiv_cancel r.length (by omega)
        obtain ⟨slotP, hslotP⟩ : ∃ slotP : Int,
            slotP = Int.fdiv (r.length * (posP.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
          ⟨_, rfl⟩
        rw [← hslotP] at hparentBorn
        have horderEq : r.order = (generatedRib ns (cause, k)).order := by rw [hrdef]; rfl
        have hposSrc : (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == idx) =
            some pos := by
          rw [← horderEq]; exact hpos
        have hposPSrc : (generatedRib ns (cause, k)).order.zipIdx.find?
            (fun v => v.1 == e.parent.toNat) = some posP := by
          rw [← horderEq]; exact hposP
        by_cases heven : e.depth % 2 = 0
        · -- even child of an odd parent: EnvStepEven
          have hoddPar : (r.entries[e.parent.toNat]'hparentLt).depth % 2 ≠ 0 := by
            have h2 := hd; have h3 := heven; omega
          have hlbP := generated_entry_parent_lower_bound ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat (src_mem _ _ heP)
          have hrootP : (r.entries[e.parent.toNat]'hparentLt).parent ≠ -1 := by
            intro hpp
            have hd2 := generated_root_depth ns cause k hlink hcause
              (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat (src_mem _ _ heP) hpp
            omega
          have hgeP : 0 ≤ (r.entries[e.parent.toNat]'hparentLt).parent := by omega
          have hownP : ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat =
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat + 1 :=
            by omega
          have hgrandLt : (r.entries[e.parent.toNat]'hparentLt).parent.toNat <
              r.entries.length := by
            have hb := (List.getElem?_eq_some_iff.mp hgrandFrame).1
            omega
          have hgrandLookup : r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]? =
              some (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt) :=
            List.getElem?_eq_getElem hgrandLt
          have heG : (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt,
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat) ∈ r.entries.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr hgrandLookup
          obtain ⟨doneG, restG, hprefixG, _⟩ := List.eq_append_cons_of_mem heG
          obtain ⟨posG, ggFrame, grandBorn, hposG, hggFrame, hgrandBornLookup, hgrandBorn⟩ :=
            hrecords doneG
              (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat restG hprefixG
          obtain ⟨slotG, hslotG⟩ : ∃ slotG : Int,
              slotG = Int.fdiv (r.length * (posG.2 + 1 : Nat)) (r.entries.length + 1 : Nat) :=
            ⟨_, rfl⟩
          rw [← hslotG] at hgrandBorn
          rw [hownP] at hgrandFrame
          have hGF : grandBorn = grandFrame :=
            Option.some.inj (hgrandBornLookup.symm.trans hgrandFrame)
          have hposGSrc : (generatedRib ns (cause, k)).order.zipIdx.find?
              (fun v => v.1 == (r.entries[e.parent.toNat]'hparentLt).parent.toNat) = some posG := by
            rw [← horderEq]; exact hposG
          have hcastP : (r.entries[e.parent.toNat]'hparentLt).parent =
              (((r.entries[e.parent.toNat]'hparentLt).parent.toNat : Nat) : Int) :=
            (Int.toNat_of_nonneg hgeP).symm
          have hdepthGP := generated_parent_child_depth ns cause k hlink hcause
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
            (r.entries[e.parent.toNat]'hparentLt)
            (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
            (src_mem _ _ heG) (src_mem _ _ heP) hcastP
          have hgrandEven : (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).depth % 2 = 0 := by
            have h2 := hdepthGP; have h3 := hoddPar
            have hm := Nat.mod_lt (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).depth (by decide : 0 < 2)
            omega
          have hoddEp := depthBone_odd_endpoints p
            ({ grandFrame with drawn := (processedOddDraws doneP
                ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat) } : Bone)
            (r.entries[e.parent.toNat]'hparentLt).depth slotP
            (children ns (r.entries[e.parent.toNat]'hparentLt).node).length
            (run p r.heights + 3) hoddPar
          rw [← hparentBorn, hPB] at hoddEp
          have hevenEpG := depthBone_even_endpoints p
            ({ ggFrame with drawn := (processedOddDraws doneG
                ((r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).parent
                  + 1).toNat) } : Bone)
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).depth slotG
            (children ns
              (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt).node).length
            (run p r.heights + 3) hgrandEven
          rw [← hgrandBorn, hGF] at hevenEpG
          have hT0G : grandFrame.t0 = slotG := hevenEpG.1
          have hT1P : parentFrame.t1 = slotP := hoddEp.2.1
          have hT0P : parentFrame.t0 = slotG := by
            have h1 : parentFrame.t0 = grandFrame.t0 := hoddEp.1
            rw [h1, hT0G]
          have hPX1 : parentFrame.x1 =
              parentFrame.x0 - run p (parentFrame.t1 - parentFrame.t0) := by
            have h1 : parentFrame.x1 =
                parentFrame.x0 - run p (slotP - grandFrame.t0) := hoddEp.2.2.2
            rw [hT1P, hT0P, h1, hT0G]
          have hchainG : IndexedAncestor (generatedRib ns (cause, k)).entries
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat idx :=
            IndexedAncestor.tail
              (IndexedAncestor.edge
                (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
                (r.entries[e.parent.toNat]'hparentLt)
                (List.mem_zipIdx_iff_getElem?.mp (src_mem _ _ heP)) hcastP)
              e (List.mem_zipIdx_iff_getElem?.mp (src_mem e idx hmem)) hparEq
          have hordGP := (generated_ancestor_order ns cause k
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
            (r.entries[e.parent.toNat]'hparentLt)
            (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
            (src_mem _ _ heG) (src_mem _ _ heP)
            (IndexedAncestor.edge
              (r.entries[e.parent.toNat]'hparentLt).parent.toNat e.parent.toNat
              (r.entries[e.parent.toNat]'hparentLt)
              (List.mem_zipIdx_iff_getElem?.mp (src_mem _ _ heP)) hcastP)
            posG posP hposGSrc hposPSrc).1 hgrandEven
          have hordGC := (generated_ancestor_order ns cause k
            (r.entries[(r.entries[e.parent.toNat]'hparentLt).parent.toNat]'hgrandLt)
            e
            (r.entries[e.parent.toNat]'hparentLt).parent.toNat idx
            (src_mem _ _ heG) (src_mem e idx hmem) hchainG posG pos hposGSrc hposSrc).1
            hgrandEven
          have hordPC := (generated_parent_child_order ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
            (src_mem _ _ heP) (src_mem e idx hmem) hparEq posP pos hposPSrc hposSrc).2 hoddPar
          have h2even : parentFrame.t0 < parentFrame.t1 := by
            rw [hT0P, hT1P, hslotG, hslotP]
            exact causeEnv_slot_strict r.length ((r.entries.length + 1 : Nat) : Int) hrlen
              (by omega) hLd posG.2 posP.2 hordGP
          have h4even : parentFrame.t0 ≤ slot := by
            rw [hT0P, hslotG, hslot]
            exact slotMono posG.2 pos.2 (by omega) (Int.le_of_lt hrlen)
          have h5even : slot ≤ parentFrame.t1 := by
            rw [hT1P, hslotP, hslot]
            exact slotMono pos.2 posP.2 (by omega) (Int.le_of_lt hrlen)
          have hsmL : parentFrame.t1 ≤ r.length := by
            rw [hT1P, hslotP]
            have hmemOP := List.mem_of_find?_eq_some hposP
            have hgetOP := List.mem_zipIdx_iff_getElem?.mp hmemOP
            have hposPLt : posP.2 < r.order.length := (List.getElem?_eq_some_iff.mp hgetOP).1
            have hordLeP : r.order.length ≤ r.entries.length := by
              rw [hrdef]
              exact Elegant.Kinds.IshikawaSeparation.generated_effective_order_length_le ns
                (measuredSideLength p ribs) cause k
            calc Int.fdiv (r.length * (posP.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
                = slotP := hslotP.symm
              _ ≤ Int.fdiv (r.length * (r.entries.length + 1 : Nat))
                  (r.entries.length + 1 : Nat) := by
                rw [hslotP]
                exact slotMono posP.2 r.entries.length (by omega) (Int.le_of_lt hrlen)
              _ = r.length := Int.mul_fdiv_cancel r.length (by omega)
          have hstepEven := env_step_even_slack r p hcos hsin (by omega)
          obtain ⟨hx0s, hx1s, hslacks⟩ := hstepEven parentFrame slot
            (children ns e.node).length hrlen
            h2even hsmL h4even h5even ihP.1
          have hbornE : born =
              depthBone p parentFrame 2 slot (children ns e.node).length (run p r.heights + 3) := by
            rw [hborn]
            exact causeEnv_depthBone_even_congr' p parentFrame
              (processedOddDraws doneE ((e.parent + 1).toNat)) e.depth 2 slot
              (children ns e.node).length (run p r.heights + 3) heven
              (by decide : (2 : Nat) % 2 = 0)
          rw [← hbornE] at hx0s hx1s hslacks
          rw [hbf]
          exact ⟨hslacks, hx1s⟩
        · -- odd child of an even parent: EnvStepOdd
          have hevenPar : (r.entries[e.parent.toNat]'hparentLt).depth % 2 = 0 := by
            have h2 := hd; have h3 := heven; omega
          have hodd : e.depth % 2 ≠ 0 := by omega
          have hPeven := depthBone_even_endpoints p
            ({ grandFrame with drawn := (processedOddDraws doneP
                ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat) } : Bone)
            (r.entries[e.parent.toNat]'hparentLt).depth slotP
            (children ns (r.entries[e.parent.toNat]'hparentLt).node).length
            (run p r.heights + 3) hevenPar
          rw [← hparentBorn, hPB] at hPeven
          have hcountP : parentFrame.count =
              ((children ns (r.entries[e.parent.toNat]'hparentLt).node).length : Int) := by
            rw [← hPB, hparentBorn]
            have hcond : ((r.entries[e.parent.toNat]'hparentLt).depth % 2 != 0) = false := by
              rw [hevenPar]; decide
            simp only [depthBone, hcond, Bool.false_eq_true, ite_false]
          obtain ⟨_, hres2⟩ := even_native_reservation p
            ({ grandFrame with drawn := (processedOddDraws doneP
                ((r.entries[e.parent.toNat]'hparentLt).parent + 1).toNat) } : Bone)
            (r.entries[e.parent.toNat]'hparentLt).depth slotP
            (children ns (r.entries[e.parent.toNat]'hparentLt).node).length
            (run p r.heights + 3) hevenPar
          rw [← hparentBorn, hPB] at hres2
          have hprefixE' : (generatedRib ns (cause, k)).entries.zipIdx =
              doneE ++ (e, idx) :: restE := hentriesEq ▸ hprefixE
          have hdrawBound := generated_current_odd_prefix_draw_bound ns cause k hlink hcause
            doneE e idx restE hprefixE' (r.entries[e.parent.toNat]'hparentLt) e.parent.toNat
            (src_mem _ _ heP) hparEq hodd
          have hordP2 := (generated_parent_child_order ns cause k
            (r.entries[e.parent.toNat]'hparentLt) e e.parent.toNat idx
            (src_mem _ _ heP) (src_mem e idx hmem) hparEq posP pos hposPSrc hposSrc).1 hevenPar
          have hstrictP : parentFrame.t0 < slot := by
            rw [hPeven.1, hslotP, hslot]
            exact causeEnv_slot_strict r.length ((r.entries.length + 1 : Nat) : Int) hrlen
              (by omega) hLd posP.2 pos.2 hordP2
          have hstepOdd := env_step_odd_slack r p hcos hsin (by omega)
          obtain ⟨hx0s, hx1s, hslacks⟩ := hstepOdd parentFrame
            (processedOddDraws doneE ((e.parent + 1).toNat)) slot (children ns e.node).length
            hrlen (by rw [hPeven.1, hPeven.2.1])
            (by rw [hcountP]; omega)
            (by rw [hownEq, hcountP]; omega)
            hstrictP hslotLen ihP.1
          have hbornO : born =
              depthBone p { parentFrame with drawn := processedOddDraws doneE ((e.parent + 1).toNat) }
                1 slot (children ns e.node).length (run p r.heights + 3) := by
            rw [hborn]
            exact causeEnv_depthBone_odd_congr p
              ({ parentFrame with drawn := processedOddDraws doneE ((e.parent + 1).toNat) } : Bone)
              e.depth 1 slot (children ns e.node).length (run p r.heights + 3) hodd
              (by decide : (1 : Nat) % 2 ≠ 0)
          rw [← hbornO] at hx0s hx1s hslacks
          rw [hbf]
          exact ⟨hslacks, hx1s⟩
  have hlt : idx < r.entries.length := by
    have hidxLt := (List.getElem?_eq_some_iff.mp hframe).1
    rw [hlength] at hidxLt
    omega
  exact (key e.depth e idx b hmem rfl hlt hframe).2

end Elegant.Kinds.IshikawaFinal
