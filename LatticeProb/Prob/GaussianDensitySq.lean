/-
The square of the Gaussian density on the line.

The square of `gaussianPDFReal m v` is a constant multiple of the density of half
the variance, so it is integrable and its integral is `(2√(πv))⁻¹`.  This is the
one-dimensional input of the Cameron--Martin entropy bound of
`prop:fixed-scale-crossings` (`sandpile.tex:2300-2400`).
-/
import Mathlib

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

open scoped NNReal

/-- **The square of the Gaussian density.**  For a nonzero variance `v`, the
square of `gaussianPDFReal m v` is `(2√(πv))⁻¹` times the density of half the
variance. -/
theorem gaussianPDFReal_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    (gaussianPDFReal m v y) ^ 2
      = (2 * Real.sqrt (Real.pi * v))⁻¹ * gaussianPDFReal m (v / 2) y := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    rcases v.coe_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (by exact_mod_cast h.symm : v = 0) hv
  have hc : ((v / 2 : NNReal) : ℝ) = (v : ℝ) / 2 := by push_cast; ring
  have hs2 : Real.sqrt (2 * Real.pi * ((v : ℝ) / 2)) = Real.sqrt (Real.pi * (v : ℝ)) := by
    congr 1
    ring
  have hexp : Real.exp (-(y - m) ^ 2 / (2 * (v : ℝ))) ^ 2
      = Real.exp (-(y - m) ^ 2 / (2 * ((v : ℝ) / 2))) := by
    rw [sq, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hsq1 : Real.sqrt (2 * Real.pi * (v : ℝ)) ^ 2 = 2 * Real.pi * (v : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt (Real.pi * (v : ℝ)) ^ 2 = Real.pi * (v : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hprod : Real.sqrt (Real.pi * (v : ℝ)) * Real.sqrt (Real.pi * (v : ℝ))
      = Real.pi * (v : ℝ) := by
    rw [← sq]
    exact hsq2
  have hconst : ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ^ 2
      = (2 * Real.sqrt (Real.pi * (v : ℝ)))⁻¹ * (Real.sqrt (Real.pi * (v : ℝ)))⁻¹ := by
    rw [inv_pow, hsq1, ← mul_inv]
    congr 1
    calc 2 * Real.pi * (v : ℝ) = 2 * (Real.pi * (v : ℝ)) := by ring
      _ = 2 * (Real.sqrt (Real.pi * (v : ℝ)) * Real.sqrt (Real.pi * (v : ℝ))) := by rw [hprod]
      _ = 2 * Real.sqrt (Real.pi * (v : ℝ)) * Real.sqrt (Real.pi * (v : ℝ)) := by ring
  simp only [gaussianPDFReal, hc, mul_pow, hexp, hs2, hconst]
  ring

/-- Half of a nonzero variance is nonzero. -/
theorem half_ne_zero_of_ne_zero {v : ℝ≥0} (hv : v ≠ 0) : (v / 2 : ℝ≥0) ≠ 0 := by
  intro h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact hv h
  · norm_num at h

/-- **The square of the Gaussian density is integrable.** -/
theorem integrable_gaussianPDFReal_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y : ℝ => (gaussianPDFReal m v y) ^ 2) := by
  have hpt : (fun y : ℝ => (gaussianPDFReal m v y) ^ 2)
      = fun y : ℝ => (2 * Real.sqrt (Real.pi * v))⁻¹ * gaussianPDFReal m (v / 2) y :=
    funext fun y => gaussianPDFReal_sq m hv y
  rw [hpt]
  exact (integrable_gaussianPDFReal m (v / 2)).const_mul _

/-- **The square of the Gaussian density integrates to `(2√(πv))⁻¹`.** -/
theorem integral_gaussianPDFReal_sq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ y : ℝ, (gaussianPDFReal m v y) ^ 2 = (2 * Real.sqrt (Real.pi * v))⁻¹ := by
  have hpt : (fun y : ℝ => (gaussianPDFReal m v y) ^ 2)
      = fun y : ℝ => (2 * Real.sqrt (Real.pi * v))⁻¹ * gaussianPDFReal m (v / 2) y :=
    funext fun y => gaussianPDFReal_sq m hv y
  rw [hpt, integral_const_mul,
    integral_gaussianPDFReal_eq_one m (half_ne_zero_of_ne_zero hv), mul_one]

end LatticeProb
