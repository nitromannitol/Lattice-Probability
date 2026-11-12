import LatticeProb.Gauss.CircleAverageCovariance
import LatticeProb.Gauss.GaussianBorelCantelli
import LatticeProb.LQG.LQGMeasure

/-!
# The law of the circle averages about the origin of a whole-plane GFF

For the whole-plane GFF normalized to have vanishing average over `∂B_1(0)`, the circle average
`h_R(0)` is a centred Gaussian of variance `|log R|`, whatever `R > 0`.  Consequently, along the
dyadic radii `2^{-j}` the variance is `j log 2`, and Borel-Cantelli gives, almost surely and for
every `η > 0`, the subexponential bound `exp(γ h_{2^{-j}}(0)) ≤ exp(η j)` for all large `j`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

open LatticeProb.LQG

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The variance of the circle average about the origin: `Var h_R(0) = 2 log max(R,1) - log R`,
i.e. `|log R|`. -/
theorem IsWholePlaneGFF.variance_circle_origin (hh : IsWholePlaneGFF P hC hcirc) {R : ℝ}
    (hR : 0 < R) :
    Var[fun ω => hcirc ω R 0; P] = 2 * Real.log (max R 1) - Real.log R := by
  have hP := hh.isProbabilityMeasure
  rw [← covariance_self (hh.hasGaussianLaw_circle hR 0).aemeasurable,
    hh.covariance_circle_circle hR hR, wholePlaneGFFCov_circle_circle_eq hR,
    circlePairPotential_self_center hR.le, max_self]
  have h : Real.circleAverage logMaxAbs 0 R = Real.log (max R 1) :=
    Real.circleAverage_const_on_circle fun x hx => by
      have hx' : ‖x‖ = R := by simpa [abs_of_pos hR] using hx
      simp only [logMaxAbs, hx']
  rw [h]
  ring

/-- **Law of the circle average about the origin.**  `h_R(0) ∼ N(0, 2 log max(R,1) - log R)`. -/
theorem IsWholePlaneGFF.hasLaw_circle_origin (hh : IsWholePlaneGFF P hC hcirc) {R : ℝ}
    (hR : 0 < R) :
    HasLaw (fun ω => hcirc ω R 0)
      (gaussianReal 0 (2 * Real.log (max R 1) - Real.log R).toNNReal) P := by
  have hG := hh.hasGaussianLaw_circle hR 0
  have hmean : ∫ ω, hcirc ω R 0 ∂P = 0 := hh.integral_eq_zero (.circle R 0) hR
  exact ⟨hG.aemeasurable, by
    rw [hG.map_eq_gaussianReal, hmean, hh.variance_circle_origin hR]⟩

/-- **Law of the dyadic circle averages about the origin.**
`h_{2^{-k}}(0) ∼ N(0, k log 2)`. -/
theorem IsWholePlaneGFF.hasLaw_circle_dyadic (hh : IsWholePlaneGFF P hC hcirc) (k : ℕ) :
    HasLaw (fun ω => hcirc ω (dyadicScale k) 0)
      (gaussianReal 0 ((k : ℝ) * Real.log 2).toNNReal) P := by
  have hr : 0 < dyadicScale k := by unfold dyadicScale; positivity
  have hr1 : dyadicScale k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := hh.hasLaw_circle_origin hr
  have hv : 2 * Real.log (max (dyadicScale k) 1) - Real.log (dyadicScale k) =
      (k : ℝ) * Real.log 2 := by
    rw [max_eq_right hr1, Real.log_one, dyadicScale, Real.log_pow, Real.log_inv]
    ring
  rwa [hv] at h

/-- **Subexponential growth of the exponential of the dyadic circle averages.**  Almost surely,
for every `η > 0`, `exp (γ h_{2^{-j}}(0)) ≤ exp (η j)` for all large `j`. -/
theorem IsWholePlaneGFF.ae_forall_eventually_exp_circle_dyadic_le
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      Real.exp (γ * hcirc ω (dyadicScale j) 0) ≤ Real.exp (η * j) := by
  have hP := hh.isProbabilityMeasure
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine GaussBC.ae_forall_eventually_exp_le (v := Real.log 2) (c := 0) hlog2
    (fun j => hh.hasLaw_circle_dyadic j) (fun j => ?_) γ
  rw [Real.coe_toNNReal _ (by positivity)]
  linarith

end LatticeProb.Gauss
