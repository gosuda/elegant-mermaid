import Elegant.Layered.DivergeTiedSweepProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem orderWithBudget_divergeChainAgree
    {p : Proper} {opts : OrderOptions} {ord : OrderResult}
    (horder : OrderImpl.orderWithBudget p opts = .ok ord)
    (hseed : DivergeChainAgree p (OrderImpl.seedBest p opts.start))
    (hsweep : ∀ (sweep : Nat) {L : List (List Nat)}, OrderImpl.Layering p L →
      OrderImpl.LayersContiguous p L → DivergeChainAgree p L →
      DivergeChainAgree p (OrderImpl.sweepLayers p sweep L opts.key))
    (htranspose : ∀ {L : List (List Nat)}, OrderImpl.Layering p L →
      DivergeChainAgree p L → DivergeChainAgree p (OrderImpl.transpose p L))
    (hnormalise : ∀ {L : List (List Nat)}, OrderImpl.Layering p L →
      OrderImpl.LayersContiguous p L → DivergeChainAgree p L →
      DivergeChainAgree p (OrderImpl.siblingNormalise p L)) :
    DivergeChainAgree p ord.layers := by
  have hrun : ∀ (fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
      OrderImpl.Layering p best → OrderImpl.LayersContiguous p best →
      DivergeChainAgree p best →
      DivergeChainAgree p (OrderImpl.runKey p opts.key OrderImpl.sweepMax
        OrderImpl.sweepStall fuel sweep best score stall).layers := by
    intro fuel
    induction fuel with
    | zero =>
      intro _ _ _ _ _ _ hbest
      exact hbest
    | succ fuel ih =>
      intro sweep best score stall hbestL hbestC hbest
      let swept := OrderImpl.sweepLayers p sweep best opts.key
      have hsweptL : OrderImpl.Layering p swept :=
        OrderImpl.sweepLayers_layering hbestL sweep opts.key
      have hsweptC : OrderImpl.LayersContiguous p swept :=
        OrderImpl.sweepLayers_contiguous p sweep best opts.key hbestC
      have hbeforeL := OrderImpl.transpose_layering hsweptL
      have hbeforeC := OrderImpl.transpose_contiguous p swept hsweptC
      have hbefore := htranspose hsweptL (hsweep sweep hbestL hbestC hbest)
      have htrial := hnormalise hbeforeL hbeforeC hbefore
      unfold OrderImpl.runKey
      dsimp only
      by_cases himp : OrderImpl.crossCount p (OrderImpl.siblingNormalise p
          (OrderImpl.transpose p (OrderImpl.sweepLayers p sweep best opts.key))) < score
      · simp only [himp, decide_true, ite_true]
        split
        · exact htrial
        · split
          · exact htrial
          · exact ih _ _ _ _ (OrderImpl.siblingNormalise_layering hbeforeL)
              (OrderImpl.siblingNormalise_contiguous hbeforeC) htrial
      · simp only [himp, decide_false, Bool.false_eq_true, ite_false]
        split
        · exact hbest
        · split
          · exact hbest
          · exact ih _ _ _ _ hbestL hbestC hbest
  unfold OrderImpl.orderWithBudget at horder
  split at horder
  · split at horder
    · simp only [Except.ok.injEq] at horder
      subst horder
      exact hrun _ _ _ _ _ (OrderImpl.seedBest_spec p opts.start).1
        (OrderImpl.seedBest_contiguous p opts.start) hseed
    · simp at horder
  · simp at horder

end Elegant.Layered.PipelineImpl
