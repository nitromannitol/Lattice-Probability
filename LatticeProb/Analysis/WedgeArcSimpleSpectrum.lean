import LatticeProb.Analysis.WedgeArcSineComplete

/-! # Simplicity of the angular sine spectrum -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- If all Fourier coefficients satisfy a diagonal eigenvalue equation with
    distinct eigenvalues, the vector is a multiple of the corresponding mode. -/
theorem hilbertBasis_eq_smul_of_diagonal_eigenvalue
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (eig : ι → ℂ)
    (heig : Function.Injective eig) (k : ι) (v : E)
    (hv : ∀ n, eig n * inner ℂ (b n) v = eig k * inner ℂ (b n) v) :
    v = inner ℂ (b k) v • b k := by
  classical
  apply b.repr.injective
  apply lp.ext
  funext n
  by_cases hnk : n = k
  · subst n
    simp [HilbertBasis.repr_apply_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  · have hc : inner ℂ (b n) v = 0 := by
      have hne : eig n - eig k ≠ 0 := sub_ne_zero.mpr (fun h => hnk (heig h))
      apply (mul_eq_zero.mp ?_).resolve_left hne
      have h := hv n
      linear_combination h
    simp [HilbertBasis.repr_apply_apply, hc, b.orthonormal.inner_eq_zero hnk]

/-- The positive angular frequencies have distinct squared eigenvalues. -/
theorem wedgeArc_sine_eigenvalues_injective {θ : ℝ} (hθ : 0 < θ) :
    Function.Injective (fun n : ℕ =>
      (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ)) := by
  intro n m h
  change (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) =
    (((Real.pi * (m + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) at h
  have heq : (Real.pi * (n + 1 : ℕ) / θ) ^ 2 =
      (Real.pi * (m + 1 : ℕ) / θ) ^ 2 := by exact_mod_cast h
  have hn : 0 < Real.pi * (n + 1 : ℕ) / θ := by positivity
  have hm : 0 < Real.pi * (m + 1 : ℕ) / θ := by positivity
  have he : Real.pi * (n + 1 : ℕ) / θ = Real.pi * (m + 1 : ℕ) / θ := by
    nlinarith
  have hcast : ((n + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by
    have hp : Real.pi / θ ≠ 0 := ne_of_gt (div_pos Real.pi_pos hθ)
    apply (mul_left_cancel₀ hp)
    simpa only [div_mul_eq_mul_div, mul_comm] using he
  exact Nat.succ.inj (by exact_mod_cast hcast)

/-- The Fourier equations for a fixed angular eigenvalue determine its
    eigenspace: it consists of multiples of the corresponding sine mode. -/
theorem wedgeArc_eq_smul_of_fourier_eigenvalue {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) (k : ℕ)
    (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ))
    (hv : ∀ n : ℕ,
      (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (wedgeArcSineLp θ n) v =
        (((Real.pi * (k + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (wedgeArcSineLp θ n) v) :
    v = inner ℂ (wedgeArcSineLp θ k) v • wedgeArcSineLp θ k := by
  simpa only [wedgeArcSineHilbertBasis_apply] using
    (hilbertBasis_eq_smul_of_diagonal_eigenvalue (wedgeArcSineHilbertBasis hθ hθ')
      (fun n => (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ))
      (wedgeArc_sine_eigenvalues_injective hθ) k v
      (by simpa only [wedgeArcSineHilbertBasis_apply] using hv))

end LatticeProb
