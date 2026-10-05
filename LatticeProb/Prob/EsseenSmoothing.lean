/-
# Esseen's smoothing inequality for a Gaussian target

For a probability measure `μ` on `ℝ` with a finite first absolute moment, a variance `v > 0`
and a cut-off `T > 0`, the Kolmogorov distance between the distribution functions of `μ` and of
`N(0, v)` satisfies, for every `x`,

  `|F_μ x - G x| ≤ (1/π) ∫_{-T}^{T} ‖φ_μ t - φ_γ t‖ / |t| dt + 64 / (π T √(2π v))`.

The proof combines the three ingredients proved in the neighbouring files:

* the deconvolution step `sup_cdf_sub_le_of_smoothed` (`EsseenDeconvolution.lean`), which needs a
  probability density `k` with a tail bound `∫_{|w| > h} k ≤ a / h`, a Lipschitz bound `m` for the
  Gaussian distribution function, and a bound `B` for the `k`-smoothed difference;
* the Fejér kernel (`FejerKernel.lean`), whose tail mass is at most `4 / (π T h)`, so that
  `a = 4 / (π T)`;
* the Fourier inversion `abs_smoothed_cdf_sub_le` (`EsseenFejerInversion.lean`), giving the bound
  `B = (1/2π) ∫_{-T}^{T} ‖φ_μ - φ_γ‖ / |t|`.

The constants combine to `2 B + 16 a m`.
-/
import Mathlib
import LatticeProb.Prob.EsseenFejerInversion
import LatticeProb.Prob.EsseenDeconvolution
import LatticeProb.Prob.GaussianBerryEsseenFacts

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- **Esseen's smoothing inequality**, Gaussian target. -/
theorem esseen_smoothing_gaussian {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => |x|) μ) {v : ℝ≥0} (hv : 0 < v) {T : ℝ} (hT : 0 < T)
    (x : ℝ) :
    |(μ (Set.Iic x)).toReal - (gaussianReal 0 v (Set.Iic x)).toReal|
      ≤ (1 / Real.pi) * (∫ t in (-T)..T,
            ‖charFun μ t - charFun (gaussianReal 0 v) t‖ / |t|)
          + 64 * (Real.sqrt (2 * Real.pi * v))⁻¹ / (Real.pi * T) := by
  have hpi := Real.pi_pos
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr hv
  have hγ : Integrable (fun x : ℝ => |x|) (gaussianReal 0 v) := integrable_abs_gaussianReal hv
  have hm : 0 < (Real.sqrt (2 * Real.pi * v))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have key := sup_cdf_sub_le_of_smoothed (μ := μ) (γ := gaussianReal 0 v) hm
    (gaussianReal_Iic_lipschitz hv) (k := fejerKernel T)
    (fun w => fejerKernel_nonneg hT w) (integrable_fejerKernel hT) (integral_fejerKernel hT)
    (a := 4 / (Real.pi * T))
    (fun h hh => by
      calc _ ≤ 4 / (Real.pi * T * h) := fejerKernel_tail hT hh
        _ = 4 / (Real.pi * T) / h := by rw [div_div])
    (B := (1 / (2 * Real.pi)) *
      ∫ t in (-T)..T, ‖charFun μ t - charFun (gaussianReal 0 v) t‖ / |t|)
    (fun x => abs_smoothed_cdf_sub_le hμ hγ hT x) x
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

end LatticeProb
