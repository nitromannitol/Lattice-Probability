import Mathlib
import LatticeProb.Gauss.CameronMartinDerived2
import LatticeProb.Gauss.RegressionResidual
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar

/-!
# Energy bound for pairings of the whole-plane Gaussian free field against smooth shifts

For `f` smooth with compact support let `q_f = -(2π)⁻¹ Δ f` (`cmTestFn f`). For the whole-plane
Gaussian free field `h` (`LatticeProb.Gauss.IsWholePlaneGFF`) and a mean-zero test function `φ`,

* `cov((h, φ), (h, q_f)) = ∫ φ f`;
* `Var(h, q_f) = (2π)⁻¹ ∫ ‖∇f‖²`;
* hence the Cameron-Martin bound `|∫ φ f| ≤ ((2π)⁻¹ ∫ ‖∇f‖²)^{1/2} · sd(h, φ)`.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Set Laplacian
open scoped ENNReal ContDiff

section Energy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The test function `q_f = -(2π)⁻¹ Δ f` has mean zero. -/
theorem integral_cmTestFn_eq_zero {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : ∫ y, cmTestFn f y = 0 := by
  unfold cmTestFn
  rw [integral_const_mul, integral_laplacian_eq_zero (hf.of_le (by norm_num)) hc, mul_zero]

/-- The covariance of the pairing with a mean-zero test function `φ` and the pairing with
`q_f = -(2π)⁻¹ Δ f` is `∫ φ f`. -/
theorem IsWholePlaneGFF.cov_pairing_cmTestFn (hh : IsWholePlaneGFF P hC hcirc) {f φ : ℂ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (hφ : IsTestFunction univ φ)
    (hφ0 : ∫ x, φ x = 0) :
    cov[fun w => hC w φ, fun w => hC w (cmTestFn f); P] = ∫ x, φ x * f x := by
  have h := hh.covariance_eq (.pairing φ) (.pairing (cmTestFn f)) hφ (cmTestFn_isTestFunction hf hc)
  simp only [GFFObservable.eval] at h
  rw [h]
  simp only [wholePlaneGFFCov, GFFObservable.smear]
  have hq : ∀ x, ∫ y, cmTestFn f y * wholePlaneCov x y = f x - Real.circleAverage f 0 1 := fun x => by
    simp_rw [mul_comm (cmTestFn f _)]
    exact integral_wholePlaneCov_mul_cmTestFn hf hc x
  simp_rw [hq]
  have hφint : Integrable φ :=
    (hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1
  have hint : Integrable (fun x => φ x * f x) :=
    ((hφ.1.continuous).mul (hf.continuous)).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hrw : ∀ x, φ x * (f x - Real.circleAverage f 0 1) =
      φ x * f x - Real.circleAverage f 0 1 * φ x := fun x => by ring
  simp_rw [hrw]
  rw [integral_sub hint (hφint.const_mul _), integral_const_mul, hφ0]
  simp

/-- The variance of the pairing with `q_f` is `(2π)⁻¹ ∫ ‖∇f‖²`. -/
theorem IsWholePlaneGFF.variance_pairing_cmTestFn (hh : IsWholePlaneGFF P hC hcirc) {f : ℂ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Var[fun w => hC w (cmTestFn f); P] = (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hq := cmTestFn_isTestFunction hf hc
  have hmeas : AEMeasurable (fun w => hC w (cmTestFn f)) P :=
    (hh.measurable_pairing _ hq).aemeasurable
  rw [← covariance_self hmeas, hh.cov_pairing_cmTestFn hf hc hq (integral_cmTestFn_eq_zero hf hc),
    QuantumZipper.K3.integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian (hf.of_le (by norm_num)) hc,
    ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [cmTestFn]
  ring

/-- **Energy bound.** For a mean-zero test function `φ` and `f` smooth with compact support,
`|∫ φ f| ≤ ((2π)⁻¹ ∫ ‖∇f‖²)^{1/2} · sd (h, φ)`. -/
theorem IsWholePlaneGFF.abs_integral_mul_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {f φ : ℂ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (hφ : IsTestFunction univ φ)
    (hφ0 : ∫ x, φ x = 0) :
    |∫ x, φ x * f x| ≤
      Real.sqrt ((2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ f x‖ ^ 2) *
        Real.sqrt Var[fun w => hC w φ; P] := by
  have hq := cmTestFn_isTestFunction hf hc
  have hL : ∀ ψ, IsTestFunction univ ψ → MemLp (fun w => hC w ψ) 2 P := fun ψ hψ => by
    have := (hh.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing ψ, hψ⟩).memLp_two
    exact this
  have hcs := covariance_sq_le_variance_mul (hL φ hφ) (hL _ hq)
  rw [hh.cov_pairing_cmTestFn hf hc hφ hφ0, hh.variance_pairing_cmTestFn hf hc] at hcs
  have hV : 0 ≤ Var[fun w => hC w φ; P] := variance_nonneg _ _
  rw [mul_comm, ← Real.sqrt_mul hV]
  exact Real.abs_le_sqrt hcs

end Energy

end LatticeProb.Gauss
