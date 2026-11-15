import LatticeProb.Analysis.IntervalDirichletGreen

/-! # Sine coefficients of a classical Dirichlet second derivative -/

set_option autoImplicit false

open MeasureTheory Set
open LQGMetric.HeatSq

namespace LatticeProb

/-- The negative second derivative of a classical Dirichlet function has sine
coefficients given by the Dirichlet eigenvalues. -/
theorem interval_sine_coefficient_neg_second_deriv {a L c : ℝ} (hL : 0 < L)
    (k : ℕ) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a (a + L)))
    (hf' : ContinuousOn f' (Icc a (a + L)))
    (hf'' : ContinuousOn f'' (Icc a (a + L)))
    (hfd : ∀ x ∈ Ioo a (a + L), HasDerivAt f (f' x) x)
    (hf'd : ∀ x ∈ Ioo a (a + L), HasDerivAt f' (f'' x) x)
    (ha : f a = 0) (hb : f (a + L) = 0) :
    (∫ x in a..a + L, (c * sinMode a L k x) * (-f'' x)) =
      (Real.pi * k / L) ^ 2 * ∫ x in a..a + L, (c * sinMode a L k x) * f x := by
  let s : ℝ → ℝ := fun x => c * sinMode a L k x
  let s' : ℝ → ℝ := deriv s
  let s'' : ℝ → ℝ := fun x => -(Real.pi * k / L) ^ 2 * s x
  have hs : Continuous s := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_const_mul_sinMode a L c k x).continuousAt
  have hs' : Continuous s' := by
    have he : s' = fun x => c * (Real.pi * k / L * Real.cos (Real.pi * k / L * (x - a))) := by
      funext x
      exact (hasDerivAt_const_mul_sinMode a L c k x).deriv
    rw [he]
    fun_prop
  have hs'' : Continuous s'' := hs.const_mul _
  have hsd : ∀ x ∈ Ioo a (a + L), HasDerivAt s (s' x) x := by
    intro x hx
    exact (hasDerivAt_const_mul_sinMode a L c k x).congr_deriv
      (hasDerivAt_const_mul_sinMode a L c k x).deriv.symm
  have hs'd : ∀ x ∈ Ioo a (a + L), HasDerivAt s' (s'' x) x := by
    intro x hx
    exact hasDerivAt_deriv_const_mul_sinMode a L c k x
  have hends := sinMode_const_mul_endpoints a L c k (ne_of_gt hL)
  have h := integral_mul_second_deriv_eq_integral_second_deriv_mul
    (by linarith : a < a + L) hs.continuousOn hf hs'.continuousOn hf'
    hs''.continuousOn hf'' hsd hfd hs'd hf'd hends.1 hends.2 ha hb
  change (∫ x in a..a + L, s x * f'' x) =
    ∫ x in a..a + L, (-(Real.pi * k / L) ^ 2 * s x) * f x at h
  have hneg : (∫ x in a..a + L, s x * (-f'' x)) =
      -(∫ x in a..a + L, s x * f'' x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hfactor : (∫ x in a..a + L, (-(Real.pi * k / L) ^ 2 * s x) * f x) =
      -(Real.pi * k / L) ^ 2 * ∫ x in a..a + L, s x * f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  change (∫ x in a..a + L, s x * (-f'' x)) = _
  rw [hneg, h, hfactor]
  ring

end LatticeProb
