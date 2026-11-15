import LatticeProb.Analysis.DirichletEigenfunction
import LatticeProb.Analysis.IntervalSineEigenmodes

/-! # Weak equation for a classical eigenfunction on an interval -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A classical eigenfunction satisfies the weak equation against every continuously
    differentiable test function vanishing at the endpoints. -/
theorem dirichlet_eigenfunction_weak {f f' g g' : ℝ → ℝ} {a b lam : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hfc : ContinuousOn f' (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f' (-lam * f x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hgc : ContinuousOn g' (Icc a b))
    (ha : g a = 0) (hb : g b = 0) :
    (∫ x in a..b, g' x * f' x) = lam * ∫ x in a..b, g x * f x := by
  have hgu : ContinuousOn g (uIcc a b) := by
    simpa [uIcc_of_le hab.le] using
      (show ContinuousOn g (Icc a b) from fun x hx => (hg x hx).continuousAt.continuousWithinAt)
  have hfu : ContinuousOn f' (uIcc a b) := by simpa [uIcc_of_le hab.le] using hfc
  have hgiu : ContinuousOn g' (uIcc a b) := by simpa [uIcc_of_le hab.le] using hgc
  have hfiu : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab.le] using hf
  have hi₁ : IntervalIntegrable g' volume a b := hgiu.intervalIntegrable
  have hi₂ : IntervalIntegrable (fun x => -lam * f x) volume a b :=
    (hfiu.const_mul (-lam)).intervalIntegrable
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hgu hfu (fun x hx => hg x (Ioo_subset_Icc_self (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hx)))
    (fun x hx => hfd x (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hx)) hi₁ hi₂
  have hl : (∫ x in a..b, g x * (-lam * f x)) =
      -lam * ∫ x in a..b, g x * f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hl, ha, hb] at h
  nlinarith

open LQGMetric.HeatSq

/-- Interval sine modes satisfy the weak Dirichlet eigenvalue equation. -/
theorem sinMode_weak_eigenfunction {a L c : ℝ} (hL : 0 < L) (k : ℕ)
    {g g' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc a (a + L), HasDerivAt g (g' x) x)
    (hgc : ContinuousOn g' (Icc a (a + L)))
    (ha : g a = 0) (hb : g (a + L) = 0) :
    (∫ x in a..a + L, g' x * deriv (fun y => c * sinMode a L k y) x) =
      (Real.pi * k / L) ^ 2 * ∫ x in a..a + L, g x * (c * sinMode a L k x) := by
  have hf : Continuous (fun y => c * sinMode a L k y) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_const_mul_sinMode a L c k x).continuousAt
  have hfd : deriv (fun y => c * sinMode a L k y) =
      fun y => c * (Real.pi * k / L * Real.cos (Real.pi * k / L * (y - a))) := by
    funext y
    exact (hasDerivAt_const_mul_sinMode a L c k y).deriv
  have hfc : Continuous (deriv (fun y => c * sinMode a L k y)) := by
    rw [hfd]
    fun_prop
  apply dirichlet_eigenfunction_weak (by linarith) hf.continuousOn hfc.continuousOn
    (fun x _ => hasDerivAt_deriv_const_mul_sinMode a L c k x) hg hgc ha hb

end LatticeProb
