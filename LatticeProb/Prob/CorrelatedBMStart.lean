import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2

/-!
# The correlated Brownian pair starts at the origin

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` with `Var(L_t) = Var(R_t) = |t|` and
`Cov(L_t, R_t) = -|t| cos(π γ² / 4)` (`IsCorrelatedBM2 γ μ`). At time `0` both coordinates are centred with variance
`twoSidedMin 0 0 = 0`, hence they vanish almost surely: `L_0 = R_0 = 0` almost surely.

## Main results
* `variance_lrCoord_zero`: `Var(L_0) = Var(R_0) = 0`.
* `ae_lrCoord_zero_eq_zero`: almost surely `lrCoord i 0 = 0`, for each coordinate `i`.
* `ae_forall_lrCoord_zero_eq_zero`, `ae_eval_zero_eq_zero`: almost surely both coordinates vanish at time `0`, i.e. the
  path takes the value `(0, 0)` at time `0`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {μ : Measure Path2}

/-- Each coordinate of the correlated Brownian pair has variance `0` at time `0`. -/
theorem variance_lrCoord_zero (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) : Var[lrCoord i 0; μ] = 0 := by
  have := hμ.isProbabilityMeasure
  have hX : MemLp (lrCoord i 0) 2 μ := (hμ.isGaussianProcess.hasGaussianLaw_eval (i, (0 : ℝ))).memLp_two
  rw [← covariance_self hX.aestronglyMeasurable.aemeasurable, hμ.covariance_eq]
  simp [twoSidedMin]

/-- **Almost surely `lrCoord i 0 = 0`**: a centred variable of variance `0` vanishes almost surely. -/
theorem ae_lrCoord_zero_eq_zero (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) : ∀ᵐ ω ∂μ, lrCoord i 0 ω = 0 := by
  have := hμ.isProbabilityMeasure
  have hX : MemLp (lrCoord i 0) 2 μ := (hμ.isGaussianProcess.hasGaussianLaw_eval (i, (0 : ℝ))).memLp_two
  have hE : evariance (lrCoord i 0) μ = 0 := by
    rw [← ofReal_variance hX, variance_lrCoord_zero hμ i, ENNReal.ofReal_zero]
  have h := (evariance_eq_zero_iff hX.aestronglyMeasurable.aemeasurable).1 hE
  filter_upwards [h] with ω hω
  rw [hω, hμ.integral_eq_zero i 0]

/-- **Almost surely both coordinates vanish at time `0`.** -/
theorem ae_forall_lrCoord_zero_eq_zero (hμ : IsCorrelatedBM2 γ μ) : ∀ᵐ ω ∂μ, ∀ i, lrCoord i 0 ω = 0 :=
  ae_all_iff.2 (ae_lrCoord_zero_eq_zero hμ)

/-- **The correlated Brownian pair starts at the origin**: almost surely `ω 0 = (0, 0)`. -/
theorem ae_eval_zero_eq_zero (hμ : IsCorrelatedBM2 γ μ) : ∀ᵐ ω ∂μ, ω 0 = 0 := by
  filter_upwards [ae_forall_lrCoord_zero_eq_zero hμ] with ω hω
  have h0 : (ω 0).1 = 0 := by simpa [lrCoord] using hω 0
  have h1 : (ω 0).2 = 0 := by simpa [lrCoord] using hω 1
  exact Prod.ext h0 h1

end LatticeProb.CorrelatedBM
