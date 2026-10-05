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


/-- **Weighted Cauchy–Schwarz.**  For a positive weight `w`,
`∫ |f| |g| ≤ (∫ w f²)^{1/2} (∫ w⁻¹ g²)^{1/2}`, by Hölder with `a = √w|f|` and
`b = |g|/√w`.  With `f = 𝓕f`, `g = 𝓕g` and `w = w_s` this is the `H^s`-`H^{−s}` duality
step. -/
theorem integral_abs_mul_le_weighted {d : ℕ} {f g w : Space d → ℝ} (hw : ∀ t, 0 < w t)
    (hf : MemLp (fun t => Real.sqrt (w t) * |f t|) 2 volume)
    (hg : MemLp (fun t => (Real.sqrt (w t))⁻¹ * |g t|) 2 volume) :
    ∫ t, |f t| * |g t|
      ≤ (∫ t, w t * f t ^ 2) ^ ((1 : ℝ) / 2)
        * (∫ t, (w t)⁻¹ * g t ^ 2) ^ ((1 : ℝ) / 2) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (Filter.Eventually.of_forall fun t =>
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (abs_nonneg _))
    (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two] at hholder
  have h1 : (fun t : Space d => Real.sqrt (w t) * |f t| * ((Real.sqrt (w t))⁻¹ * |g t|))
      = fun t => |f t| * |g t| := by
    funext t
    have hw' : Real.sqrt (w t) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (hw t))
    field_simp
  rw [h1] at hholder
  refine hholder.trans (le_of_eq ?_)
  have e2 : (∫ t, (Real.sqrt (w t) * |f t|) ^ 2) = ∫ t, w t * f t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [mul_pow, Real.sq_sqrt (hw t).le, sq_abs])
  have e3 : (∫ t, ((Real.sqrt (w t))⁻¹ * |g t|) ^ 2) = ∫ t, (w t)⁻¹ * g t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [mul_pow, inv_pow, Real.sq_sqrt (hw t).le, sq_abs])
  rw [e2, e3]

end LatticeProb.Sobolev
