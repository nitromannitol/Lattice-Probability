import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lebesgue integrals of the exponential density over intervals

For `q > 0`, the density `t ↦ q e^{-q t}` of the exponential law has the following integrals,
valued in `ℝ≥0∞`:

* `lintegral_laplace_Ico`: `∫⁻_{[a, b)} q e^{-q t} dt = e^{-q a} - e^{-q b}` for `a ≤ b`;
* `lintegral_laplace_Ici`: `∫⁻_{[a, ∞)} q e^{-q t} dt = e^{-q a}`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace LatticeProb

/-- The exponential density `q e^{-q t}` integrates over `[a, b)` to `e^{-q a} - e^{-q b}`. -/
theorem lintegral_laplace_Ico {q a b : ℝ} (hq : 0 < q) (hab : a ≤ b) :
    ∫⁻ t in Set.Ico a b, ENNReal.ofReal (q * Real.exp (-(q * t))) =
      ENNReal.ofReal (Real.exp (-(q * a))) - ENNReal.ofReal (Real.exp (-(q * b))) := by
  have hcont : Continuous fun t : ℝ => q * Real.exp (-(q * t)) := by fun_prop
  have hint : IntegrableOn (fun t : ℝ => q * Real.exp (-(q * t))) (Set.Ico a b) :=
    (hcont.integrableOn_Icc (a := a) (b := b)).mono_set Set.Ico_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun t => by positivity)]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -Real.exp (-(q * t)))
      (q * Real.exp (-(q * x))) x := fun x => by
    have h1 : HasDerivAt (fun t : ℝ => -(q * t)) (-q) x := by
      simpa using ((hasDerivAt_id' x).const_mul q).fun_neg
    have h2 := (Real.hasDerivAt_exp (-(q * x))).comp x h1
    exact (h2.neg).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hcont.intervalIntegrable a b)]
  rw [← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  congr 1
  ring

/-- The exponential density `q e^{-q t}` integrates over `[a, ∞)` to `e^{-q a}`. -/
theorem lintegral_laplace_Ici {q a : ℝ} (hq : 0 < q) :
    ∫⁻ t in Set.Ici a, ENNReal.ofReal (q * Real.exp (-(q * t))) =
      ENNReal.ofReal (Real.exp (-(q * a))) := by
  have hexp : ∀ t : ℝ, Real.exp (-(q * t)) = Real.exp (-q * t) := fun t => by rw [neg_mul]
  have hint : IntegrableOn (fun t : ℝ => q * Real.exp (-(q * t))) (Set.Ioi a) := by
    simp_rw [hexp]
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hq) a).const_mul q
  rw [← setLIntegral_congr Ioi_ae_eq_Ici,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => by positivity)]
  simp_rw [hexp]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.2 hq)]
  congr 1
  field_simp

end LatticeProb
