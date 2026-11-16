import LatticeProb.Analysis.Schauder.DirichletInverse

/-!
# Bounded derivatives of the Dirichlet inverse

Ported from the Lattice-High-Contrast-Homogenization development, module
`LatticeHC.Support.Heat.SineSeriesBounded` (its first declaration).

The Dirichlet inverse `u = (−DΔ_Q)⁻¹ f` of a test function and every iterated derivative of `u` are
bounded on all of `ℝ^d`, by the sum of the termwise bounds of the sine series.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- Every iterated derivative of the Dirichlet inverse of a test function is bounded on `ℝ^d`. -/
theorem exists_bound_iteratedFDeriv_dirichletInverse (hd : 1 ≤ d) {D : ℝ} (hD : 0 < D)
    (f : Euc d → ℝ) (hf : Sobolev.IsTestFn (unitCube d) f) (j : ℕ) :
    ∃ M : ℝ, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (dirichletInverse D f) x‖ ≤ M := by
  have hv : Summable fun k : Fin d → ℕ => Real.sqrt 2 ^ d * d ^ j *
      (dirichletEigenvalue k ^ j * |(D * dirichletEigenvalue k)⁻¹ * sineCoeff f k|) :=
    (summable_pow_mul_abs_inverseCoeff hd hD f hf j).mul_left _
  obtain ⟨M, hM⟩ := hv
  refine ⟨M, fun x => ?_⟩
  rw [iteratedFDeriv_dirichletInverse hd hD f hf j x]
  exact tsum_of_norm_bounded hM fun k => norm_iteratedFDeriv_inverseTerm_le _ k j x

end LatticeProb.Analysis.Schauder
