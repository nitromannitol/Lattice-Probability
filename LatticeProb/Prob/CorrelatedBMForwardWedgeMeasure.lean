import LatticeProb.Prob.CorrelatedBMForwardWedgeEvent

/-! # Forward Brownian wedge survival probabilities -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A strict barrier and the corresponding translated forward wedge survival event
have the same probability under the Brownian law. -/
theorem measure_openSymmetricWedgeBarrier_eq_normalized_forward
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ)
    (a b q : ℝ) (ha : a ≠ 0) (T : ℝ≥0) :
    μ (openSymmetricWedgeBarrier a b q T) =
      μ {ω | ∀ t ≤ T,
        let z := Complex.orthonormalBasisOneI.repr.symm
          (normalizedWedgeStart a q + normalizedForwardSpace t ω)
        (z.re, z.im) ∈ openSymmetricWedge a b} := by
  apply measure_congr
  filter_upwards [ae_forall_lrCoord_zero_eq_zero hμ] with ω hω
  exact propext (mem_openSymmetricWedgeBarrier_iff_normalized_forward a b q ha T ω hω)

end LatticeProb.CorrelatedBM
