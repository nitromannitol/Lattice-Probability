import LatticeProb.Analysis.WedgeAngularMode
import LatticeProb.Analysis.DirichletEigenvalueBound

/-! # Classical Dirichlet eigenvalues on a symmetric interval -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The sine mode attains the least eigenvalue among nonzero classical
Dirichlet eigenfunctions on an interval of positive length. -/
theorem wedge_classical_dirichlet_eigenvalue_minimal {θ : ℝ} (hθ : 0 < θ) :
    (∃ f f' : ℝ → ℝ,
      (∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt f (f' x) x) ∧
      ContinuousOn f' (Icc (-θ / 2) (θ / 2)) ∧
      (∀ x ∈ Ioo (-θ / 2) (θ / 2),
        HasDerivAt f' (-((Real.pi / θ) ^ 2) * f x) x) ∧
      f (-θ / 2) = 0 ∧ f (θ / 2) = 0 ∧
      ∃ x ∈ Icc (-θ / 2) (θ / 2), f x ≠ 0) ∧
    (∀ (f f' : ℝ → ℝ) (lam : ℝ),
      (∀ x ∈ Icc (-θ / 2) (θ / 2), HasDerivAt f (f' x) x) →
      ContinuousOn f' (Icc (-θ / 2) (θ / 2)) →
      (∀ x ∈ Ioo (-θ / 2) (θ / 2), HasDerivAt f' (-lam * f x) x) →
      f (-θ / 2) = 0 → f (θ / 2) = 0 →
      (∃ x ∈ Icc (-θ / 2) (θ / 2), f x ≠ 0) →
      (Real.pi / θ) ^ 2 ≤ lam) := by
  have he : -θ / 2 + θ = θ / 2 := by ring
  constructor
  · let f : ℝ → ℝ := wedgeAngularMode θ
    let f' : ℝ → ℝ := fun x =>
      Real.pi / θ * Real.cos (Real.pi / θ * (x - (-θ / 2)))
    refine ⟨f, f', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact LQGMetric.HeatSq.hasDerivAt_sinShift (Real.pi / θ) (-θ / 2) x
    · dsimp [f']
      fun_prop
    · intro x hx
      exact LQGMetric.HeatSq.hasDerivAt_cosShift (Real.pi / θ) (-θ / 2) x
    · exact (wedgeAngularMode_endpoints hθ).1
    · exact (wedgeAngularMode_endpoints hθ).2
    · refine ⟨0, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · change wedgeAngularMode θ 0 ≠ 0
        rw [wedgeAngularMode_zero hθ]
        norm_num
  · intro f f' lam hd hc hd' ha hb hne
    apply dirichlet_eigenvalue_lower_bound (a := -θ / 2) hθ
    · simpa only [he] using hd
    · simpa only [he] using hc
    · simpa only [he] using hd'
    · exact ha
    · simpa only [he] using hb
    · simpa only [he] using hne

end LatticeProb
