import LatticeProb.Analysis.HarmonicBridge

/-! # Harmonicity and linear isometries -/

set_option autoImplicit false

open InnerProductSpace Filter
open scoped Laplacian

namespace LatticeProb

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The Laplacian is invariant under a real linear isometry. -/
theorem laplacian_comp_linearIsometryEquiv (f : F → ℝ) (e : E ≃ₗᵢ[ℝ] F) (x : E) :
    Δ (f ∘ e) x = Δ f (e x) := by
  let v := stdOrthonormalBasis ℝ E
  have hd := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
    f (uniqueDiffOn_univ) (Set.mem_univ (e x)) 2
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hd
  change iteratedFDeriv ℝ 2 (f ∘ e) x =
    (iteratedFDeriv ℝ 2 f (e x)).compContinuousLinearMap
      (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap) at hd
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ e) v,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (v.map e)]
  simp only [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Pulling a harmonic function back along a real linear isometry preserves harmonicity. -/
theorem harmonicAt_comp_linearIsometryEquiv {f : F → ℝ} (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (hf : HarmonicAt f (e x)) : HarmonicAt (f ∘ e) x := by
  constructor
  · exact hf.1.comp x e.toContinuousLinearEquiv.contDiff.contDiffAt
  · have h := e.continuous.continuousAt.tendsto.eventually hf.2
    filter_upwards [h] with y hy
    rw [Pi.zero_apply, laplacian_comp_linearIsometryEquiv, hy]
    rfl

end LatticeProb
