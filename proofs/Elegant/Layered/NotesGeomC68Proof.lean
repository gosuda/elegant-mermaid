import Elegant.Layered.NotesFlatLabelClauses
import Elegant.Layered.NotesMirrorFacts
import Elegant.Layered.NotesPlacementFacts
import Elegant.Layered.NotesLabelGeomFacts
import Elegant.Layered.NotesC8aRoleRepair
import Elegant.Layered.NotesRouteFacts

set_option autoImplicit false

open Elegant Layered PipelineImpl

/-!
# Note-stage C6/C8a geometry and fragment first-wins (residuals).

Proved here:
* `NotesC6Geom` from the single bridge `Nc68C6BridgeW` plus local
  well-formedness (`nc68C6Geom_of_bridgeW`). The two exclusivity conjuncts come
  from the box mirrors (`ngfC6BoxExclC/F_holds` via `notesContractMirror_holds` /
  `notesFragMirror_holds`); the other eight are reassembled from the bridge.
* `NotesC8aGeomT` from the single bridge `Nc68C8aBridgeW` plus local
  well-formedness (`nc68C8aGeomT_of_bridgeW`). The repaired role conjunct comes
  from `notesC8aContractRoleT_holds`; the other eleven are reassembled.
* Guarded `notesFragFirstWins` from lookup uniqueness
  (`nc68_fragFirstWins_of_unique` via `notesFirstMatch_holds`).

Open as ONE public named def per clause: `Nc68C6BridgeW` (eight open C6 conjuncts
plus the three mirror primitives) and `Nc68C8aBridgeW` (eleven open C8aT
conjuncts plus the contracted-mirrors-folded premise). Both strictly on
executed `NotesExecution` runs, real geometric content, neither the goal
renamed nor logically stronger alone (each needs `WellFormed` nodup for its
derived conjunct).

False as stated: unconditional `notesFragFirstWins` over arbitrary fragment
lists. Witness: `p1` with box `("x", ⟨0,0,1,1⟩)`, `dx/dy = 0/0` and `p2` with the
same box id, `dx/dy = 10/0`. Then `p2.rect "x" = some ⟨10,0,1,1⟩` but
`[p1,p2].findSome? (·.rect "x") = some ⟨0,0,1,1⟩`, so the `p2` instance fails.
True form (proved): on executed fragments with holding-rect (`hSelf`) and
cross-absence (`hCross`), the lookup returns the holding fragment; this is what
`notesFragBoxFirst` consumes via `notesFragBoxFirst_holds`.

Probe (`proofs/wip/Probe/NotesGeomC68T_probe.lean`): `self/cross/baseC/top/len/
roleT/fRole/found/clear` and `ancC/ancF/flagsKept/flagsFrag/keptFrag/fragCon/
fragOther/routerClear` are all `true` on state, group, two-note, empty-text,
and zero-size inputs; the self-loop input is rejected with
`LayoutError.domain`. C8aT `topNodup/fold/len/contractScene/cRoleT/mirror/
fRole/found/clear/fragDisj/sceneAnc/env/envDisj` are all `true` on state,
group, solo, bare-group, empty, and two-note inputs
(`NotesC8aRoleRepair.lean` `#eval ncrrGeomTBool`).
-/

/-- C6 bridge: the eight open C6 conjuncts plus the three mirror primitives
that yield the two exclusivities with local nodup. -/
def Nc68C6BridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC6AncC e ∧ NotesC6AncF e ∧ NotesC6FlagsKept e ∧ NotesC6FlagsFrag e ∧
    NotesC6KeptFrag e ∧ NotesC6FragContracted e ∧ NotesC6FragOther e ∧
    NotesC6RouterClear e ∧ NotesBaseContract e ∧ NotesBaseFrag e ∧ NotesFragRoots e

/-- C8a bridge: the eleven open C8aT conjuncts plus the contracted-mirrors-folded
premise that yields the repaired role conjunct with local nodup. -/
def Nc68C8aBridgeW {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC8aTopNodup e ∧ NotesC8aFold e ∧ NotesC8aLen e ∧ NotesC8aContractScene e ∧
    NotesC8aFragRole e ∧ NotesC8aFragFound e ∧ NotesC8aClear e ∧ NotesC8aFragDisj e ∧
    NotesC8aSceneAnc e ∧ NotesC8aEnv e ∧ NotesC8aEnvDisj e ∧
    (∀ cg ∈ e.contracted.scene.boxes, ∃ fb ∈ (e.layouts.foldl contractOne inp).boxes,
      fb.id = cg.id ∧ cg.role = fb.role.id)

/-- C8a geometry (true role form) from the bridge and local well-formedness. -/
theorem nc68C8aGeomT_of_bridgeW
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hW : Nc68C8aBridgeW e) :
    NotesC8aGeomT e := by
  obtain ⟨htop, hfold, hlen, hcs, hfr, hff, hclr, hfd, hsa, henv, henvd, hmir⟩ := hW
  have hnd : (inp.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hcrT := notesC8aContractRoleT_holds e hnd hmir
  exact ⟨htop, hfold, hlen, hcs, hcrT, hfr, hff, hclr, hfd, hsa, henv, henvd⟩

/-- C6 geometry from the bridge and local well-formedness. -/
theorem nc68C6Geom_of_bridgeW
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hW : Nc68C6BridgeW e) :
    NotesC6Geom e := by
  obtain ⟨hAncC, hAncF, hFK, hFF, hKF, hFC, hFO, hRC, hBC, hBF, hRoots⟩ := hW
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hCM := notesContractMirror_holds e hBC
  have hFRM := notesFragMirror_holds e hBF hRoots hnd
  have hExclC := ngfC6BoxExclC_holds e hCM hnd
  have hExclF := ngfC6BoxExclF_holds e hFRM hnd
  exact ⟨hAncC, hAncF, hFK, hFF, hExclC, hExclF, hKF, hFC, hFO, hRC⟩

/-- Guarded first-wins: on executed fragments with holding-rect and cross-absence,
the fragment lookup for each route-end id returns the holding fragment. This is the
true form the consumer (`notesFragBoxFirst_holds`) needs; the unconditional form
over arbitrary fragment lists is false (see header witness). -/
theorem nc68_fragFirstWins_of_unique
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {r : ModelRoute}
    (hSelf : ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect))
    (hCross : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none) :
    notesFragFirstWins e.fragments r := by
  have hFM := notesFirstMatch_holds e hSelf hCross
  intro id hid p hp b hmem hbid
  have h := hFM p hp b hmem
  rw [hbid] at h
  exact h
