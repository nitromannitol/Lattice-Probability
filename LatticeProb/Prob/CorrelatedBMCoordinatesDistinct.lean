import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2

/-!
# The two coordinates of a correlated Brownian pair are distinct

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` with `Var(L_t) = Var(R_t) = |t|` and
`Cov(L_t, R_t) = -|t| cos(π γ² / 4)` (`IsCorrelatedBM2 γ μ`). The increment `L_1 - R_1` is a centred Gaussian variable
of variance `2 + 2 cos(π γ² / 4)`, which is positive as soon as `cos(π γ² / 4) ≠ -1`, in particular for `0 < γ < 2`.
A Gaussian variable of positive variance has no atoms, so almost surely `L_1 ≠ R_1`, and hence the two coordinate
paths `t ↦ L_t` and `t ↦ R_t` are distinct.

## Main results
* `variance_lrCoord_one_sub`: `Var(L_1 - R_1) = 2 + 2 cos(π γ² / 4)`.
* `ae_lrCoord_one_ne`: almost surely `L_1 ≠ R_1`, when `cos(π γ² / 4) ≠ -1`.
* `ae_coordinatePaths_ne`, `ae_coordinatePaths_ne_of_lt_two`: almost surely the two coordinate paths are distinct.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {μ : Measure Path2}

/-- The variance of `L_1 - R_1` for the correlated Brownian pair is `2 + 2 cos(π γ² / 4)`. -/
theorem variance_lrCoord_one_sub (hμ : IsCorrelatedBM2 γ μ) :
    Var[fun ω => lrCoord 0 1 ω - lrCoord 1 1 ω; μ] = 2 + 2 * Real.cos (Real.pi * γ ^ 2 / 4) := by
  have := hμ.isProbabilityMeasure
  have hG := hμ.isGaussianProcess
  have hL : MemLp (lrCoord 0 1) 2 μ := (hG.hasGaussianLaw_eval ((0 : Fin 2), (1 : ℝ))).memLp_two
  have hR : MemLp (lrCoord 1 1) 2 μ := (hG.hasGaussianLaw_eval ((1 : Fin 2), (1 : ℝ))).memLp_two
  have h1 : twoSidedMin 1 1 = 1 := by norm_num [twoSidedMin]
  have hVL : Var[lrCoord 0 1; μ] = 1 := by
    rw [← covariance_self hL.aestronglyMeasurable.aemeasurable, hμ.covariance_eq, h1]
    simp [lrCov]
  have hVR : Var[lrCoord 1 1; μ] = 1 := by
    rw [← covariance_self hR.aestronglyMeasurable.aemeasurable, hμ.covariance_eq, h1]
    simp [lrCov]
  have hC : cov[lrCoord 0 1, lrCoord 1 1; μ] = -Real.cos (Real.pi * γ ^ 2 / 4) := by
    rw [hμ.covariance_eq, h1]
    simp [lrCov]
  have hsub := variance_sub hL hR
  rw [show (fun ω => lrCoord 0 1 ω - lrCoord 1 1 ω) = lrCoord 0 1 - lrCoord 1 1 from rfl, hsub, hVL, hVR, hC]
  ring

/-- **Almost surely `L_1 ≠ R_1`.** If `cos(π γ² / 4) ≠ -1`, the Gaussian variable `L_1 - R_1` has positive variance,
hence no atom at `0`. -/
theorem ae_lrCoord_one_ne (hμ : IsCorrelatedBM2 γ μ) (hγ : Real.cos (Real.pi * γ ^ 2 / 4) ≠ -1) :
    ∀ᵐ ω ∂μ, lrCoord 0 1 ω ≠ lrCoord 1 1 ω := by
  have := hμ.isProbabilityMeasure
  have hD : HasGaussianLaw (fun ω => lrCoord 0 1 ω - lrCoord 1 1 ω) μ :=
    hμ.isGaussianProcess.hasGaussianLaw_fun_sub (s := ((0 : Fin 2), (1 : ℝ))) (t := ((1 : Fin 2), (1 : ℝ)))
  have hv : (Var[fun ω => lrCoord 0 1 ω - lrCoord 1 1 ω; μ]).toNNReal ≠ 0 := by
    rw [variance_lrCoord_one_sub hμ]
    have hc : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := lt_of_le_of_ne (Real.neg_one_le_cos _) hγ.symm
    intro h
    rw [Real.toNNReal_eq_zero] at h
    linarith
  have hnull : μ ((fun ω => lrCoord 0 1 ω - lrCoord 1 1 ω) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hD.aemeasurable (measurableSet_singleton 0),
      hD.map_eq_gaussianReal]
    have := nullSingletonClass_gaussianReal (μ := μ[fun ω => lrCoord 0 1 ω - lrCoord 1 1 ω]) hv
    exact measure_singleton 0
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  exact sub_eq_zero.2 (not_not.1 hω)

/-- **The two coordinate paths are almost surely distinct**, when `cos(π γ² / 4) ≠ -1`. -/
theorem ae_coordinatePaths_ne (hμ : IsCorrelatedBM2 γ μ) (hγ : Real.cos (Real.pi * γ ^ 2 / 4) ≠ -1) :
    ∀ᵐ ω ∂μ, (fun t => lrCoord 0 t ω) ≠ fun t => lrCoord 1 t ω := by
  filter_upwards [ae_lrCoord_one_ne hμ hγ] with ω hω h
  exact hω (congrFun h 1)

/-- For `0 < γ < 2`, `cos(π γ² / 4) > -1`. -/
theorem neg_one_lt_cos_of_lt_two (hγ0 : 0 < γ) (hγ2 : γ < 2) : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := by
  have hlt : Real.pi * γ ^ 2 / 4 < Real.pi := by
    have : γ ^ 2 < 4 := by nlinarith
    nlinarith [Real.pi_pos]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hlt
  rwa [Real.cos_pi] at h

/-- **The two coordinate paths are almost surely distinct** for `0 < γ < 2`. -/
theorem ae_coordinatePaths_ne_of_lt_two (hμ : IsCorrelatedBM2 γ μ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂μ, (fun t => lrCoord 0 t ω) ≠ fun t => lrCoord 1 t ω :=
  ae_coordinatePaths_ne hμ (neg_one_lt_cos_of_lt_two hγ0 hγ2).ne'

end LatticeProb.CorrelatedBM
