import LatticeProb.Analysis.WedgeArcSymmetricSpectrum

/-! # Finite sine core on a circular arc -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The diagonal operator on the finite span of an orthonormal family. -/
noncomputable def orthonormalDiagonalCore {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v : ι → E} (hv : Orthonormal ℂ v) (eig : ι → ℝ) :
    Submodule.span ℂ (Set.range v) →ₗ[ℂ] E :=
  (Finsupp.linearCombination ℂ (fun i => (eig i : ℂ) • v i)).comp
    hv.linearIndependent.repr

/-- Each member of the family is an eigenvector of the finite core. -/
theorem orthonormalDiagonalCore_apply_mode {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v : ι → E} (hv : Orthonormal ℂ v) (eig : ι → ℝ) (i : ι) :
    orthonormalDiagonalCore hv eig ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ =
      (eig i : ℂ) • v i := by
  classical
  have hr : hv.linearIndependent.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ =
      Finsupp.single i 1 := by
    apply hv.linearIndependent.repr_eq
    simp
  simp [orthonormalDiagonalCore, hr]

/-- The finite sine-span operator with the angular Dirichlet eigenvalues. -/
noncomputable def wedgeArcSineCore {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    Submodule.span ℂ (Set.range (wedgeArcSineLp θ)) →ₗ[ℂ]
      Lp ℂ 2 (wedgeArcSurfaceMeasure θ) :=
  orthonormalDiagonalCore (orthonormal_wedgeArcSineLp hθ hθ')
    (fun n => (Real.pi * (n + 1 : ℕ) / θ) ^ 2)

/-- Each normalized angular sine mode belongs to the core and is an eigenvector. -/
theorem wedgeArcSineCore_apply_mode {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) :
    wedgeArcSineCore hθ hθ'
      ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩ =
      (((Real.pi * (n + 1 : ℕ) / θ) ^ 2 : ℝ) : ℂ) • wedgeArcSineLp θ n :=
  orthonormalDiagonalCore_apply_mode (orthonormal_wedgeArcSineLp hθ hθ') _ n

end LatticeProb
