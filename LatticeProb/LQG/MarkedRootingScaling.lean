import Mathlib
import LatticeProb.LQG.MarkedRootingCircle
import LatticeProb.Analysis.TestFunctionLogIntegrable
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Rescaled test functions and the reference shift

For `c > 0` and a test function `φ` the rescaled test function is `ψ(x) = c² φ(c x)`; pairings of the dilated field
`h(c ·) - h_c(0)` against `ψ` are the pairings of `h` against `φ` (up to the circle average, which is killed when
`∫ φ = 0`). This file collects the deterministic facts about the rescaling:

* `scaledTest_isTestFunction`, `scaledTest_support`, `integral_scaledTest_mul`: the rescaled function is a test
  function supported in the unit disk if `φ` is supported in the disk of radius `c`, and integrals against it
  change variables.
* `integral_scaledTest_shift`: for `∫ φ = 0` the shift
  `∫ ψ(x) Cov (h(x), h(z / c)) dx - ∫ ψ(x) (- log max(1/c, |x|)) dx` equals `∫ φ(y) Cov (h(y), h(z)) dy`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Gauss

/-- The rescaled test function `x ↦ c² φ(c x)`. -/
noncomputable def scaledTest (c : ℝ) (φ : ℂ → ℝ) : ℂ → ℝ := fun x => c ^ 2 * φ (c • x)

theorem scaledTest_isTestFunction {c : ℝ} (hc : 0 < c) {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    IsTestFunction Set.univ (scaledTest c φ) := by
  refine ⟨?_, ?_, Set.subset_univ _⟩
  · exact contDiff_const.mul (hφ.1.comp (contDiff_const_smul c))
  · have h1 : HasCompactSupport fun x : ℂ => φ (c • x) :=
      hφ.2.1.comp_homeomorph (Homeomorph.smulOfNeZero c hc.ne')
    exact h1.mul_left (f := fun _ => c ^ 2)

theorem scaledTest_support {c : ℝ} (hc : 0 < c) {φ : ℂ → ℝ} (hφ : ∀ y, φ y ≠ 0 → ‖y‖ < c) {x : ℂ}
    (hx : scaledTest c φ x ≠ 0) : ‖x‖ < 1 := by
  have h1 : φ (c • x) ≠ 0 := fun h => hx (by rw [scaledTest, h, mul_zero])
  have h2 := hφ _ h1
  rw [norm_smul, Real.norm_of_nonneg hc.le] at h2
  by_contra hcon
  have hcon' := not_lt.1 hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon' hc.le]

/-- **Change of variables for the rescaled test function.** -/
theorem integral_scaledTest_mul {c : ℝ} (hc : 0 < c) (φ : ℂ → ℝ) (G : ℂ → ℝ) :
    ∫ x, scaledTest c φ x * G x = ∫ y, φ y * G (c⁻¹ • y) := by
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun y : ℂ => φ y * G (c⁻¹ • y)) c
  simp only [Complex.finrank_real_complex, inv_smul_smul₀ hc.ne'] at h
  have h2 : ∫ x, scaledTest c φ x * G x = c ^ 2 * ∫ x, φ (c • x) * G x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [scaledTest]
    ring
  have hpos : (0 : ℝ) < (c ^ 2)⁻¹ := by positivity
  rw [h2, h, smul_eq_mul, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'),
    one_mul]

theorem integral_scaledTest {c : ℝ} (hc : 0 < c) (φ : ℂ → ℝ) :
    ∫ x, scaledTest c φ x = ∫ y, φ y := by
  have := integral_scaledTest_mul hc φ (fun _ => 1)
  simpa using this

/-- Pointwise form of the reference shift on the support of the rescaled test function. -/
theorem wholePlaneCov_scaled_add_log {c : ℝ} (hc : 0 < c) {y z : ℂ} (hy : ‖y‖ < c) (hyz : y ≠ z) :
    wholePlaneCov (c⁻¹ • y) (c⁻¹ • z) + Real.log (max c⁻¹ ‖c⁻¹ • y‖) =
      wholePlaneCov y z + (Real.log (max (c⁻¹ * ‖z‖) 1) - Real.log (max ‖z‖ 1)) := by
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hd : 0 < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hyz)
  have hyn : ‖c⁻¹ • y‖ = c⁻¹ * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hci.le]
  have hzn : ‖c⁻¹ • z‖ = c⁻¹ * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hci.le]
  have hdn : ‖c⁻¹ • y - c⁻¹ • z‖ = c⁻¹ * ‖y - z‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hci.le]
  have hlt : c⁻¹ * ‖y‖ < 1 := by
    have : c⁻¹ * ‖y‖ < c⁻¹ * c := mul_lt_mul_of_pos_left hy hci
    rwa [inv_mul_cancel₀ hc.ne'] at this
  have hmax1 : max (c⁻¹ * ‖y‖) 1 = 1 := max_eq_right hlt.le
  have hmax2 : max c⁻¹ (c⁻¹ * ‖y‖) = c⁻¹ * max 1 ‖y‖ := by
    rw [mul_max_of_nonneg _ _ hci.le, mul_one]
  have hM : 0 < max (c⁻¹ * ‖z‖) 1 := lt_max_of_lt_right one_pos
  have hA : 0 < max ‖y‖ 1 := lt_max_of_lt_right one_pos
  have hB : 0 < max ‖z‖ 1 := lt_max_of_lt_right one_pos
  have hA' : 0 < max 1 ‖y‖ := lt_max_of_lt_left one_pos
  unfold wholePlaneCov
  rw [hyn, hzn, hdn, hmax1, hmax2, one_mul, max_comm 1 ‖y‖,
    Real.log_div hM.ne' (mul_pos hci hd).ne', Real.log_mul hci.ne' hA.ne',
    Real.log_mul hci.ne' hd.ne', Real.log_div (mul_pos hA hB).ne' hd.ne', Real.log_mul hA.ne' hB.ne']
  ring

/-- **The reference shift under rescaling.** For `φ` with `∫ φ = 0` supported in the disk of radius `c`,
`∫ ψ(x) Cov (h(x), h(z / c)) dx - ∫ ψ(x) (- log max(1/c, |x|)) dx = ∫ φ(y) Cov (h(y), h(z)) dy`
for `ψ = scaledTest c φ`. -/
theorem integral_scaledTest_shift {c : ℝ} (hc : 0 < c) {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ)
    (hφ0 : ∫ x, φ x = 0) (hφs : ∀ y, φ y ≠ 0 → ‖y‖ < c) (z : ℂ) :
    (∫ x, scaledTest c φ x * wholePlaneCov x (c⁻¹ • z)) -
        ∫ x, scaledTest c φ x * -Real.log (max c⁻¹ ‖x‖) =
      ∫ y, φ y * wholePlaneCov y z := by
  have hψ := scaledTest_isTestFunction hc hφ
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have i1 : Integrable fun x => scaledTest c φ x * wholePlaneCov x (c⁻¹ • z) :=
    (TestFunctionLogIntegrable.integrable_test_mul_wholePlaneCov hψ (c⁻¹ • z)).congr
      (Filter.Eventually.of_forall fun x => by simp only [wholePlaneCov_symm x (c⁻¹ • z)]; rfl)
  have i2 : Integrable fun x => scaledTest c φ x * Real.log (max c⁻¹ ‖x‖) :=
    LatticeProb.LQG.AffineDerived.integrable_test_mul_continuous hψ
      (Continuous.log (continuous_const.max continuous_norm) fun x =>
        (lt_max_of_lt_left hci).ne')
  have h1 : (∫ x, scaledTest c φ x * wholePlaneCov x (c⁻¹ • z)) -
        ∫ x, scaledTest c φ x * -Real.log (max c⁻¹ ‖x‖) =
      ∫ x, scaledTest c φ x * (wholePlaneCov x (c⁻¹ • z) + Real.log (max c⁻¹ ‖x‖)) := by
    simp_rw [mul_neg, mul_add]
    rw [integral_neg, integral_add i1 i2, sub_neg_eq_add]
  rw [h1, integral_scaledTest_mul hc φ (fun x => wholePlaneCov x (c⁻¹ • z) + Real.log (max c⁻¹ ‖x‖))]
  have hz : ∀ᵐ y : ℂ, y ≠ z := by
    rw [ae_iff]
    simp
  have h2 : (fun y => φ y * (wholePlaneCov (c⁻¹ • y) (c⁻¹ • z) + Real.log (max c⁻¹ ‖c⁻¹ • y‖))) =ᵐ[volume]
      fun y => φ y * wholePlaneCov y z +
        (Real.log (max (c⁻¹ * ‖z‖) 1) - Real.log (max ‖z‖ 1)) * φ y := by
    filter_upwards [hz] with y hy
    by_cases h0 : φ y = 0
    · simp [h0]
    · rw [wholePlaneCov_scaled_add_log hc (hφs y h0) hy]
      ring
  rw [integral_congr_ae h2, integral_add
    (TestFunctionLogIntegrable.integrable_test_mul_wholePlaneCov hφ z |>.congr
      (Filter.Eventually.of_forall fun y => by simp only [wholePlaneCov_symm y z]; rfl))
    ((hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).const_mul _),
    integral_const_mul, hφ0, mul_zero, add_zero]

end LatticeProb.Gauss
