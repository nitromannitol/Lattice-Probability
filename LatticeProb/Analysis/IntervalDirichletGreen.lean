import LatticeProb.Analysis.DirichletWeakEigenfunction

/-! # Green's identity on an interval -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Integration by parts for a function vanishing at both endpoints. -/
theorem integral_mul_second_deriv_eq_neg_integral_deriv_mul_deriv
    {f f' g' g'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g' (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgd : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hf' : ContinuousOn f' (Icc a b)) (hg'' : ContinuousOn g'' (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    (∫ x in a..b, f x * g'' x) = -(∫ x in a..b, f' x * g' x) := by
  have hfcont : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab.le] using hf
  have hgcont : ContinuousOn g' (uIcc a b) := by simpa [uIcc_of_le hab.le] using hgc
  have hfi : IntervalIntegrable f' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab.le] using hf'
  have hgi : IntervalIntegrable g'' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab.le] using hg''
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hfcont hgcont
    (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hfd)
    (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hgd) hfi hgi
  simpa [ha, hb] using h

/-- The classical second derivative is symmetric for Dirichlet boundary values. -/
theorem integral_mul_second_deriv_eq_integral_second_deriv_mul
    {f f' f'' g g' g'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hf' : ContinuousOn f' (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hf'' : ContinuousOn f'' (Icc a b)) (hg'' : ContinuousOn g'' (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hf'd : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hg'd : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hfa : f a = 0) (hfb : f b = 0) (hga : g a = 0) (hgb : g b = 0) :
    (∫ x in a..b, f x * g'' x) = ∫ x in a..b, f'' x * g x := by
  rw [integral_mul_second_deriv_eq_neg_integral_deriv_mul_deriv
    hab hf hg' hfd hg'd hf' hg'' hfa hfb]
  have h := integral_mul_second_deriv_eq_neg_integral_deriv_mul_deriv
    hab hg hf' hgd hf'd hg' hf'' hga hgb
  simpa only [mul_comm] using h.symm

end LatticeProb
