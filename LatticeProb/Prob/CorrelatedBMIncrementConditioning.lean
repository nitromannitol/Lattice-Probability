import LatticeProb.Prob.CorrelatedBMSeparatedHalves
import LatticeProb.Prob.IncrementSigmaHalfPaths
import LatticeProb.Prob.IndependentExtensionConditioning

/-! # Conditioning centered increments of a correlated Brownian pair -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- The centered past and future of a correlated Brownian pair are conditionally
independent given the increments on their common segment. -/
theorem condIndepEv_increment_past_future {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {a b : ℝ} (hab : a ≤ b) :
    CondIndepEv (incrementSigma lrCoord (Icc a b) a)
      (incrementSigma lrCoord (Iic b) b) (incrementSigma lrCoord (Ici a) a) μ := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hmeas (T : Set ℝ) (c : ℝ) : incrementSigma lrCoord T c ≤ (inferInstance : MeasurableSpace Path2) := by
    refine iSup_le fun i => iSup_le fun t => iSup_le fun _ => ?_
    exact measurable_iff_comap_le.mp (measurable_coneIncr i t c)
  have hind : Indep (incrementSigma lrCoord (Iic b) b)
      (incrementSigma lrCoord (Ici b) b) μ := by
    rw [incrementSigma_past_eq_comap, incrementSigma_future_eq_comap]
    apply (IndepFun_iff_Indep _ _ _).mp
    simpa only [coneIncr, neg_one_mul, one_mul, sub_eq_add_neg] using
      (indepFun_centered_opposite_halves hμ (d := 1) (by norm_num) b)
  exact (condIndepEv_sup_of_indep (incrementSigma_segment_le_past lrCoord hab)
    (hmeas _ _) (hmeas _ _) hind).mono le_rfl (incrementSigma_future_le lrCoord hab)

end LatticeProb.CorrelatedBM
