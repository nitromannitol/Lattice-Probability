import LatticeProb.Analysis.WedgeArcSineClosureFourier

/-! # Fourier characterization of the angular sine core -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

private theorem diagonalPMap_eq_of_family_eq {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v w : ι → E} (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (h : v = w) (eig : ι → ℝ) :
    (show E →ₗ.[ℂ] E from ⟨_, orthonormalDiagonalCore hv eig⟩) =
      (show E →ₗ.[ℂ] E from ⟨_, orthonormalDiagonalCore hw eig⟩) := by
  subst w
  rfl

/-- The product-L² graph closure of the angular sine core is characterized
by its sine Fourier coefficients. -/
theorem wedgeArcSinePMap_graph_closure_iff {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    (x y : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) :
    (x, y) ∈ (wedgeArcSinePMap hθ hθ').graph.topologicalClosure ↔
      ∀ n : ℕ, inner ℂ (wedgeArcSineLp θ n) y =
        (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (wedgeArcSineLp θ n) x := by
  let b := wedgeArcSineHilbertBasis hθ hθ'
  let eig : ℕ → ℝ := fun n => (Real.pi * (n + 1 : ℕ) / θ) ^ 2
  have hv : (b : ℕ → Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) = wedgeArcSineLp θ := by
    funext n
    exact wedgeArcSineHilbertBasis_apply hθ hθ' n
  have hop : (show Lp ℂ 2 (wedgeArcSurfaceMeasure θ) →ₗ.[ℂ]
      Lp ℂ 2 (wedgeArcSurfaceMeasure θ) from
      ⟨_, orthonormalDiagonalCore b.orthonormal eig⟩) = wedgeArcSinePMap hθ hθ' := by
    exact diagonalPMap_eq_of_family_eq b.orthonormal
      (orthonormal_wedgeArcSineLp hθ hθ') hv eig
  have h := hilbertBasis_diagonal_graph_closure_iff b eig x y
  rw [hop] at h
  simpa only [hv] using h

end LatticeProb
