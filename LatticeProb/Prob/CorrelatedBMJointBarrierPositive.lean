import LatticeProb.Prob.CorrelatedBMWedgeSurvivalPositive
import LatticeProb.Prob.CorrelatedBMNoCommonContour

/-! # Positive survival for a correlated Brownian joint barrier -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A strict symmetric wedge barrier is contained in the corresponding closed barrier. -/
theorem openSymmetricWedgeBarrier_subset (a b q h : ℝ) :
    openSymmetricWedgeBarrier a b q h ⊆ symmetricWedgeBarrier a b q h := by
  intro ω hω t ht
  exact (hω t ht).le

/-- A correlated Brownian pair has positive probability to stay above a negative
level on a finite positive time interval. -/
theorem measure_jointZeroBarrier_pos {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hμ : IsCorrelatedBM2 γ μ)
    {q : ℝ} (hq : 0 < q) {T : ℝ≥0} (hT : T ≠ 0) :
    0 < μ (jointZeroBarrier q T) := by
  have ha : 0 < Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 :=
    div_pos (Real.sqrt_pos.2 (by linarith [one_add_lrCov_pos hγ0 hγ2])) (by norm_num)
  rw [measure_jointZeroBarrier_eq_symmetricWedge hγ0 hγ2 q T]
  exact lt_of_lt_of_le
    (measure_openSymmetricWedgeBarrier_whitened_pos hγ0 hγ2 hμ 0 ha hq hT)
    (measure_mono (openSymmetricWedgeBarrier_subset _ _ _ _))

end LatticeProb.CorrelatedBM
