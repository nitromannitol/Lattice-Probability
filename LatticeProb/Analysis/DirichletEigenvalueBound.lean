import LatticeProb.Analysis.DirichletInterval
import LatticeProb.Analysis.DirichletEigenfunction

/-! # Lower bound for a classical Dirichlet eigenvalue -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A nonzero classical Dirichlet eigenfunction on an interval of length `θ`
has eigenvalue at least `(π / θ)^2`. -/
theorem dirichlet_eigenvalue_lower_bound {f f' : ℝ → ℝ} {a θ lam : ℝ}
    (hθ : 0 < θ)
    (hd : ∀ x ∈ Icc a (a + θ), HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc a (a + θ)))
    (hd' : ∀ x ∈ Ioo a (a + θ), HasDerivAt f' (-lam * f x) x)
    (ha : f a = 0) (hb : f (a + θ) = 0)
    (hne : ∃ x ∈ Icc a (a + θ), f x ≠ 0) :
    (Real.pi / θ) ^ 2 ≤ lam := by
  have hab : a < a + θ := by linarith
  have hfc : ContinuousOn f (Icc a (a + θ)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hn := interval_integral_sq_pos_of_ne_zero hab hfc hne
  have he := dirichlet_eigenfunction_energy hab hd hc hd' ha hb
  have hi := dirichlet_interval_inequality hθ hd hc ha hb
  rw [he] at hi
  have hfac : 1 ≤ (θ / Real.pi) ^ 2 * lam := by
    refine le_of_mul_le_mul_right ?_ hn
    simpa only [one_mul, mul_assoc] using hi
  have hprod : (Real.pi / θ) ^ 2 * (θ / Real.pi) ^ 2 = 1 := by
    field_simp
  calc
    (Real.pi / θ) ^ 2 = (Real.pi / θ) ^ 2 * 1 := by ring
    _ ≤ (Real.pi / θ) ^ 2 * ((θ / Real.pi) ^ 2 * lam) :=
      mul_le_mul_of_nonneg_left hfac (sq_nonneg _)
    _ = lam := by rw [← mul_assoc, hprod, one_mul]

end LatticeProb
