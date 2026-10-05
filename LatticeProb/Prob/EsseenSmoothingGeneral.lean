/-
# Esseen's smoothing inequality for a general target with a Lipschitz distribution function

`EsseenSmoothing.lean` proves Esseen's smoothing inequality for a **Gaussian** target.  The route
`scratch/pk/mvbe-route.md`, step A3, asks for the general pair form, comparing two arbitrary
probability measures whose target distribution function is Lipschitz.  This file lands it: for
probability measures `μ, γ` on `ℝ` with finite first absolute moments and `γ`'s distribution
function `m`-Lipschitz, and every cut-off `T > 0`,

  `|F_μ x − F_γ x| ≤ (1/π) ∫_{−T}^{T} ‖φ_μ t − φ_γ t‖ / |t| dt`
  `+ 64 m / (π T)` .

The Gaussian case is the instance `γ = gaussianReal 0 v`, `m = (√(2π v))⁻¹`, which is exactly
`LatticeProb.esseen_smoothing_gaussian`.

The proof is the same three-ingredient combination as there — the deconvolution step
`sup_cdf_sub_le_of_smoothed` (`EsseenDeconvolution.lean`) with the Fejér kernel, the tail bound
`fejerKernel_tail` (`a = 4/(π T)`), and the Fourier inversion `abs_smoothed_cdf_sub_le`
(`EsseenFejerInversion.lean`) — with only the Gaussian-specific Lipschitz input
`gaussianReal_Iic_lipschitz` replaced by the hypothesis `hG`.  The constants combine to
`2 B + 16 a m`.
-/
import Mathlib
import LatticeProb.Prob.EsseenSmoothing

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- **Esseen's smoothing inequality**, general target.  The target `γ` need only have a Lipschitz
distribution function (`hG`, with constant `m > 0`) and a finite first absolute moment. -/
theorem esseen_smoothing {μ γ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ : Integrable (fun x : ℝ => |x|) μ) (hγ : Integrable (fun x : ℝ => |x|) γ)
    {m : ℝ} (hm : 0 < m)
    (hG : ∀ x y : ℝ, |(γ (Set.Iic x)).toReal - (γ (Set.Iic y)).toReal| ≤ m * |x - y|)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (γ (Set.Iic x)).toReal|
      ≤ (1 / Real.pi) * (∫ t in (-T)..T, ‖charFun μ t - charFun γ t‖ / |t|)
          + 64 * m / (Real.pi * T) := by
  have key := sup_cdf_sub_le_of_smoothed (μ := μ) (γ := γ) hm hG
    (k := fejerKernel T) (fun w => fejerKernel_nonneg hT w)
    (integrable_fejerKernel hT) (integral_fejerKernel hT)
    (a := 4 / (Real.pi * T))
    (fun h hh => by
      calc _ ≤ 4 / (Real.pi * T * h) := fejerKernel_tail hT hh
        _ = 4 / (Real.pi * T) / h := by rw [div_div])
    (B := (1 / (2 * Real.pi)) * ∫ t in (-T)..T, ‖charFun μ t - charFun γ t‖ / |t|)
    (fun x => abs_smoothed_cdf_sub_le hμ hγ hT x) x
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The Gaussian specialization of the general smoothing inequality.**  With the Lipschitz CDF
constant `(√(2π v))⁻¹` of `N(0, v)` this is the Gaussian smoothing inequality
`esseen_smoothing_gaussian` (`EsseenSmoothing.lean`), here recovered as an instance of
`esseen_smoothing`. -/
theorem esseen_smoothing_gaussian_of_general {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => |x|) μ) {v : ℝ≥0} (hv : 0 < v) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (gaussianReal 0 v (Set.Iic x)).toReal|
      ≤ (1 / Real.pi) * (∫ t in (-T)..T,
            ‖charFun μ t - charFun (gaussianReal 0 v) t‖ / |t|)
          + 64 * (Real.sqrt (2 * Real.pi * v))⁻¹ / (Real.pi * T) :=
  esseen_smoothing hμ (integrable_abs_gaussianReal hv)
    (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) (gaussianReal_Iic_lipschitz hv) hT x

end LatticeProb
