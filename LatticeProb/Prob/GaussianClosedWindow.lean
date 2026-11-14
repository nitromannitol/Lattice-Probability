import LatticeProb.Bonanno.MatedCRTHarmonic.Brownian.OneStep

/-! # Gaussian interval bound

A nondegenerate centered Gaussian assigns a closed interval at most its
length times the maximum of its density, uniformly in the interval's center.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace LatticeProb

/-- A closed Gaussian window has mass at most its length times the maximum
of the Gaussian density. The estimate holds for every real radius. -/
theorem gaussianReal_Icc_le {v : ℝ≥0} (hv : v ≠ 0) (a r : ℝ) :
    gaussianReal 0 v (Icc (a - r) (a + r)) ≤
      ENNReal.ofReal (2 * r * (√(2 * π * v))⁻¹) := by
  let : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
  rw [← measure_congr (Ioo_ae_eq_Icc : Ioo (a - r) (a + r) =ᵐ[gaussianReal 0 v] Icc (a - r) (a + r))]
  exact MatedCRTHarmonic.Brownian.gaussianReal_Ioo_le hv a r

end LatticeProb
