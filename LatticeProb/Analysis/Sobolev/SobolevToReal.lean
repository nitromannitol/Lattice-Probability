/-
# The real-integral form of the Sobolev norm

`sobolevNormSq_toReal_eq_integral` converts the extended-real Sobolev norm `sobolevNormSq` into
the Bochner integral of the weighted squared Fourier modulus, under the integrability of that
weighted modulus.  The bridge is Mathlib's `ofReal_integral_eq_lintegral_ofReal` followed by
`ENNReal.toReal_ofReal`.
-/
import LatticeProb.Analysis.Sobolev.SobolevYoungConvolution

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- If the weighted squared Fourier modulus is integrable, the real part of the squared `H^s`
norm is its Bochner integral. -/
theorem sobolevNormSq_toReal_eq_integral {d : ℕ} (s : ℝ) {f : Space d → ℝ}
    (h : Integrable (fun ξ : Space d => sobolevWeight s ξ *
          ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2)) :
    (sobolevNormSq d s f).toReal
      = ∫ ξ, sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 := by
  rw [sobolevNormSq_eq_lintegral_weight s f,
    ← ofReal_integral_eq_lintegral_ofReal h
      (Filter.Eventually.of_forall fun ξ =>
        mul_nonneg (sobolevWeight_nonneg s ξ) (by positivity)),
    ENNReal.toReal_ofReal]
  exact integral_nonneg fun ξ => mul_nonneg (sobolevWeight_nonneg s ξ) (by positivity)

end LatticeProb.Sobolev
