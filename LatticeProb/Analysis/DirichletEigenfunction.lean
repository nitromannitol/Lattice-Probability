import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Energy of a classical Dirichlet eigenfunction -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Integration by parts identifies the energy of a Dirichlet eigenfunction. -/
theorem dirichlet_eigenfunction_energy {f f' : ℝ → ℝ} {a b lam : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc a b))
    (hd' : ∀ x ∈ Ioo a b, HasDerivAt f' (-lam * f x) x)
    (ha : f a = 0) (hb : f b = 0) :
    (∫ x in a..b, f' x ^ 2) = lam * ∫ x in a..b, f x ^ 2 := by
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hfu : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab.le] using hfc
  have hdu : ContinuousOn f' (uIcc a b) := by simpa [uIcc_of_le hab.le] using hc
  have hi₁ : IntervalIntegrable f' volume a b := hdu.intervalIntegrable
  have hi₂ : IntervalIntegrable (fun x => -lam * f x) volume a b :=
    (hfu.const_mul (-lam)).intervalIntegrable
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hfu hdu (fun x hx => hd x (Ioo_subset_Icc_self (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hx)))
    (fun x hx => hd' x (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hx)) hi₁ hi₂
  have hl : (∫ x in a..b, f x * (-lam * f x)) =
      -lam * ∫ x in a..b, f x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hr : (∫ x in a..b, f' x * f' x) = ∫ x in a..b, f' x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hl, hr, ha, hb] at h
  nlinarith

/-- A continuous function nonzero at a point has positive squared integral. -/
theorem interval_integral_sq_pos_of_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hne : ∃ x ∈ Icc a b, f x ≠ 0) :
    0 < ∫ x in a..b, f x ^ 2 := by
  apply intervalIntegral.integral_pos hab (hf.pow 2)
  · intro x hx
    exact sq_nonneg (f x)
  · obtain ⟨x, hx, hfx⟩ := hne
    exact ⟨x, hx, sq_pos_of_ne_zero hfx⟩

end LatticeProb
