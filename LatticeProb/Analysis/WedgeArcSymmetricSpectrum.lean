import LatticeProb.Analysis.WedgeArcSimpleSpectrum

/-! # Symmetric operators with angular sine eigenvectors -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- Symmetry on a linear domain turns eigenvector equations for a Hilbert
basis and one further eigenvector into the corresponding Fourier equations. -/
theorem hilbertBasis_fourier_eq_of_symmetric
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (D : Submodule ℂ E)
    (T : D →ₗ[ℂ] E) (eig : ι → ℝ)
    (hsym : ∀ u v : D, inner ℂ (T u) (v : E) = inner ℂ (u : E) (T v))
    (hb : ∀ n, b n ∈ D)
    (hmode : ∀ n, T ⟨b n, hb n⟩ = (eig n : ℂ) • b n)
    (k : ι) (v : D) (hv : T v = (eig k : ℂ) • (v : E)) :
    ∀ n, (eig n : ℂ) * inner ℂ (b n) (v : E) =
      (eig k : ℂ) * inner ℂ (b n) (v : E) := by
  intro n
  have h := hsym ⟨b n, hb n⟩ v
  rw [hmode n, hv, inner_smul_left, inner_smul_right] at h
  have hc : (starRingEnd ℂ) (eig n : ℂ) = (eig n : ℂ) :=
    RCLike.conj_ofReal (eig n)
  rw [hc] at h
  exact h

/-- An eigenvector of a symmetric operator whose domain contains all the
angular sine modes is a multiple of the mode with the same eigenvalue. -/
theorem wedgeArc_eq_smul_of_symmetric_eigenvector {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    (D : Submodule ℂ (Lp ℂ 2 (wedgeArcSurfaceMeasure θ)))
    (T : D →ₗ[ℂ] Lp ℂ 2 (wedgeArcSurfaceMeasure θ))
    (hsym : ∀ u v : D, inner ℂ (T u) (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) =
      inner ℂ (u : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) (T v))
    (hb : ∀ n, wedgeArcSineLp θ n ∈ D)
    (hmode : ∀ n, T ⟨wedgeArcSineLp θ n, hb n⟩ =
      (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) • wedgeArcSineLp θ n)
    (k : ℕ) (v : D)
    (hv : T v = (((Real.pi * (k + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) •
      (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ))) :
    (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) =
      inner ℂ (wedgeArcSineLp θ k) (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) •
        wedgeArcSineLp θ k := by
  apply wedgeArc_eq_smul_of_fourier_eigenvalue hθ hθ' k
  have h := hilbertBasis_fourier_eq_of_symmetric (wedgeArcSineHilbertBasis hθ hθ')
    D T (fun n => (Real.pi * (n + 1 : ℕ) / θ) ^ 2) hsym
    (by simpa only [wedgeArcSineHilbertBasis_apply] using hb)
    (by simpa only [wedgeArcSineHilbertBasis_apply] using hmode) k v hv
  simpa only [wedgeArcSineHilbertBasis_apply] using h

end LatticeProb
