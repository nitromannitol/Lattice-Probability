/-
# The Cauchy–Schwarz (duality) bound for the convolution value

The `C^m`-boundedness of the mollified family `{f ⋆ ρ}` — the remaining input to
`FrechetKolmogorovMollifiedCompact` — starts from the pointwise Cauchy–Schwarz bound
`|(f ⋆ ρ)(x)| ≤ ‖f‖_{L²} ‖ρ(x−·)‖_{L²}`, which feeds the `H^s`-`H^{−s}` duality
bound of `AbsApply.lean`.  It is `integral_mul_le_Lp_mul_Lq_of_nonneg` at `p = q = 2`
applied to the convolution integral.
-/
import LatticeProb.Analysis.Sobolev.SobolevConvolution

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- **Cauchy–Schwarz for the convolution value.** -/
theorem abs_convReal_le {d : ℕ} {f ρ : Space d → ℝ} (hf : MemLp f 2 volume) (x : Space d)
    (hρx : MemLp (fun t : Space d => ρ (x - t)) 2 volume) :
    |convReal f ρ x|
      ≤ (∫ t, |f t| ^ 2) ^ ((1 : ℝ) / 2) * (∫ t, |ρ (x - t)| ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [convReal, convolution_def]
  refine (abs_integral_le_integral_abs).trans ?_
  have hcongr : (∫ t, |(ContinuousLinearMap.mul ℝ ℝ) (f t) (ρ (x - t))|)
      = ∫ t, |f t| * |ρ (x - t)| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [abs_mul]
  rw [hcongr]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t => abs_nonneg _)
    (Filter.Eventually.of_forall fun t => abs_nonneg _)
    (by simpa using hf.norm) (by simpa using hρx.norm)
  simp only [Real.rpow_two] at hholder
  exact hholder

end LatticeProb.Sobolev
