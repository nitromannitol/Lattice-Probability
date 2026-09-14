/-
Scaling of the Fourier-side Sobolev norm: `‖c φ‖²_{H^s} = c² ‖φ‖²_{H^s}`.
-/
import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The `H^s` norm is homogeneous of degree two: scaling a test function by a
constant scales its squared norm by the square of the constant. -/
theorem sobolevNormSq_const_mul (d : ℕ) (s c : ℝ) (φ : Space d → ℝ) :
    sobolevNormSq d s (fun x => c * φ x) = ENNReal.ofReal (c ^ 2) * sobolevNormSq d s φ := by
  rw [sobolevNormSq, sobolevNormSq]
  have hpt : ∀ ξ : Space d,
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => ((c * φ x : ℝ) : ℂ)) ξ‖ ^ 2)
        = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    have hf : 𝓕 (fun x : Space d => ((c * φ x : ℝ) : ℂ)) ξ = (c : ℂ) * 𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ := by
      rw [Real.fourier_eq, Real.fourier_eq]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      rw [Circle.smul_def, Circle.smul_def, Complex.ofReal_mul]
      ring
    rw [hf, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c ^ 2)]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (|c| * ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖) ^ 2
        = c ^ 2 * ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2 by rw [mul_pow, sq_abs]]
    ring
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end LatticeProb.Sobolev
