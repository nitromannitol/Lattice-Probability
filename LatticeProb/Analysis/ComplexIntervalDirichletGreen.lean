import LatticeProb.Analysis.DirichletWeakEigenfunction

/-! # Complex Green identity on an interval -/

set_option autoImplicit false

open MeasureTheory Set ComplexConjugate

namespace LatticeProb

/-- Integration by parts for complex functions when the first function vanishes at
both endpoints. -/
theorem integral_complex_mul_second_deriv_eq_neg_integral_deriv_mul_deriv
    {f f' g' g'' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
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

/-- The classical complex second derivative is symmetric for Dirichlet boundary
values, with conjugation in the first argument. -/
theorem integral_conj_mul_second_deriv_eq_integral_conj_second_deriv_mul
    {f f' f'' g g' g'' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hf' : ContinuousOn f' (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hf'' : ContinuousOn f'' (Icc a b)) (hg'' : ContinuousOn g'' (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hf'd : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hg'd : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hfa : f a = 0) (hfb : f b = 0) (hga : g a = 0) (hgb : g b = 0) :
    (∫ x in a..b, conj (f x) * g'' x) = ∫ x in a..b, conj (f'' x) * g x := by
  have hc : Continuous (conj : ℂ → ℂ) := Complex.continuous_conj
  have hcd : ∀ {u u' : ℝ → ℂ} {x : ℝ}, HasDerivAt u (u' x) x →
      HasDerivAt (fun y => conj (u y)) (conj (u' x)) x := by
    intro u u' x hu
    exact Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hu
  have h₁ := integral_complex_mul_second_deriv_eq_neg_integral_deriv_mul_deriv
    hab (hc.comp_continuousOn hf) hg' (fun x hx => hcd (hfd x hx)) hg'd
    (hc.comp_continuousOn hf') hg'' (by simp [hfa]) (by simp [hfb])
  change (∫ x in a..b, conj (f x) * g'' x) =
    -(∫ x in a..b, conj (f' x) * g' x) at h₁
  rw [h₁]
  have h := integral_complex_mul_second_deriv_eq_neg_integral_deriv_mul_deriv
    hab hg (hc.comp_continuousOn hf') hgd (fun x hx => hcd (hf'd x hx))
    hg' (hc.comp_continuousOn hf'') hga hgb
  simpa only [Function.comp_apply, mul_comm] using h.symm

end LatticeProb
