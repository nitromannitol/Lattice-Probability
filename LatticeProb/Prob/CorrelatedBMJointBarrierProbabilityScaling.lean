import LatticeProb.Prob.CorrelatedBMBarrierScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling

/-! # Brownian scaling of joint barrier probabilities -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- A unit-time joint barrier estimate uniform in the correlated Brownian law
transfers to any positive time horizon with its barrier rescaled by `√h`. -/
theorem measure_jointZeroBarrier_le_of_unit {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (q h : ℝ) (hh : 0 < h) (J : ℝ≥0∞)
    (hJ : ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν →
      ν (jointZeroBarrier (q / Real.sqrt h) 1) ≤ J) :
    μ (jointZeroBarrier q h) ≤ J := by
  have hb := hJ (μ.map (unitRescalePath h))
    (isCorrelatedBM2_map_unitRescalePath hh hμ)
  rw [Measure.map_apply (measurable_unitRescalePath h)
    (measurableSet_jointZeroBarrier _ _ (by norm_num))] at hb
  have heq : (unitRescalePath h) ⁻¹' jointZeroBarrier (q / Real.sqrt h) 1 =
      jointZeroBarrier q h := by
    ext ω
    exact jointZeroBarrier_scaled_iff ω q h hh
  rwa [heq] at hb

end LatticeProb.CorrelatedBM
