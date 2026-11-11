import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Calculus of the Laplacian of a real function on a Euclidean space

For a real-valued function `f` on a finite-dimensional real inner product space `E`, the Laplacian
`Laplacian.laplacian f` (Mathlib's `InnerProductSpace.Laplacian`) is the trace of the second Fréchet
derivative: `Δ f x = ∑ᵢ D²f x (eᵢ, eᵢ)` for any orthonormal basis `(eᵢ)` of `E`. This file records three
elementary properties of this operator on functions of class `C²`:

* continuity of `Δ f`;
* vanishing of `Δ f` outside the topological support of `f`;
* commutation of `Δ` with translations of the argument.
-/

namespace LatticeProb.LaplacianCalculus

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of a `C²` real function on a finite-dimensional real inner product space is
continuous. It is the sum of the continuous maps `x ↦ D²f x (eᵢ, eᵢ)` over an orthonormal basis. -/
theorem continuous_laplacian_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have hc : Continuous (iteratedFDeriv ℝ 2 f) := hf.continuous_iteratedFDeriv le_rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f]
  exact continuous_finsetSum _ fun i _ =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
      ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]).continuous.comp hc

/-- The Laplacian of a real function vanishes at every point outside the topological support of the
function, since the function is eventually zero near such a point. -/
theorem laplacian_eq_zero_off_tsupport {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) :
    Laplacian.laplacian f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  have h := (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds
  rw [h]
  simp

/-- The Laplacian commutes with translation of the argument:
`Δ (fun w ↦ f (w + z)) x = (Δ f) (x + z)`. -/
theorem laplacian_comp_add_right (f : E → ℝ) (z x : E) :
    Laplacian.laplacian (fun w => f (w + z)) x = Laplacian.laplacian f (x + z) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun w => f (w + z)),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f]
  simp only [iteratedFDeriv_comp_add_right]

end LatticeProb.LaplacianCalculus
