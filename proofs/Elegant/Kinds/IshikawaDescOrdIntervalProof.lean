import Elegant.Kinds.IshikawaDescRouteClearance
import Elegant.IshikawaFlattenClausesProof

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant
open Elegant.Ishikawa

theorem descendantOrdInterval (ns : List Tree.Node) (cause k : Nat) :
    DescendantOrdInterval ns cause k := by
  intro eI eJ idxI idxJ posI posJ hmI hmJ hfindI hfindJ hoddne hlt hpos
  have hfields := (generated_rib_fields ns cause k).2.2.1
  have he : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst hfields
  have ho : (generatedRib ns (cause, k)).order =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 :=
    congrArg Prod.snd hfields
  obtain ⟨segE, segO, hflat, _hsegB, _hinv, hoddW⟩ :=
    flatJointFlatten ns (upper k) 64 (children ns cause) (-1) 2 0 [] []
      (by simp) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) flatInvNil flatWinOddNil
  have hfst : (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1
      = segE := by
    have := congrArg Prod.fst hflat
    simpa using this
  have hsnd : (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2
      = segO := by
    have := congrArg Prod.snd hflat
    simpa using this
  have heE : (generatedRib ns (cause, k)).entries = segE := by rw [he, hfst]
  have hoO : (generatedRib ns (cause, k)).order = segO := by rw [ho, hsnd]
  have hae' : segE[idxI]? = some eI := by
    have hmI' : (eI, idxI) ∈ segE.zipIdx := by rwa [heE] at hmI
    exact List.mem_zipIdx_iff_getElem?.mp hmI'
  have hej' : segE[idxJ]? = some eJ := by
    have hmJ' : (eJ, idxJ) ∈ segE.zipIdx := by rwa [heE] at hmJ
    exact List.mem_zipIdx_iff_getElem?.mp hmJ'
  have hpa' : segO[posI.2]? = some idxI := by
    have hfindI' : segO.zipIdx.find? (fun v => v.1 == idxI) = some posI := by
      rwa [hoO] at hfindI
    exact flatFoundSlot _ _ _ hfindI'
  have hpj' : segO[posJ.2]? = some idxJ := by
    have hfindJ' : segO.zipIdx.find? (fun v => v.1 == idxJ) = some posJ := by
      rwa [hoO] at hfindJ
    exact flatFoundSlot _ _ _ hfindJ'
  have hwin := hoddW idxI idxJ eI eJ posI.2 posJ.2 hae' hej' hoddne hlt hpa' hpj'
    (by omega)
  rw [heE]
  simpa using hwin

end Elegant.Kinds.IshikawaFinal
