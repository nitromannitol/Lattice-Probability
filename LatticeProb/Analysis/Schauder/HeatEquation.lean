import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.KernelDerivTime
import LatticeProb.Analysis.Schauder.SineCoeff

/-!
# The heat equation for the Gaussian kernel

At positive times the Gaussian heat kernel `p_t` on `ℝ^d` satisfies `Δ p_t = ∂_t p_t`: the Laplacian
`Σ_i ∂_i² p_t(x) = (‖x‖²/(4t²) - d/(2t)) p_t(x)` is the sum of the second-derivative coefficients
`x_i²/(4t²) - 1/(2t)` of `KernelDerivSpace`, which `KernelDerivTime` identifies with the time
coefficient of `p_t(x)`.
-/

namespace LatticeProb.Analysis.Schauder

open Real

open scoped InnerProductSpace

noncomputable section

variable {d : ℕ}

/-- **The heat equation** for the Gaussian kernel: `Δ p_t = ∂_t p_t`, written with the explicit
time coefficient. -/
theorem laplacianSum_heatKernel {t : ℝ} (ht : 0 < t) (x : Euc d) :
    laplacianSum (heatKernel d t) x =
      (-(d : ℝ) / (2 * t) + ‖x‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t x := by
  rw [laplacianSum_eq_sum_dirDeriv ((contDiff_heatKernel t).of_le le_top)]
  have hsummand : ∀ i : Fin d,
      dirDeriv (EuclideanSpace.single i 1)
          (dirDeriv (EuclideanSpace.single i 1) (heatKernel d t)) x =
        ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel d t x := by
    intro i
    have h := fderiv_fderiv_heatKernel_apply ht x (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1)
    have hx : ⟪x, EuclideanSpace.single i (1 : ℝ)⟫_ℝ = x i := by
      simp [EuclideanSpace.inner_single_right]
    have hs : ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)⟫_ℝ = 1 := by
      simp
    rw [hx, hs] at h
    unfold dirDeriv
    rw [h]
    ring
  simp_rw [hsummand]
  rw [← Finset.sum_mul, sum_heatKernel_coeff]

/-- The heat equation in derivative form: the time derivative of `p_t(x)` is `Δ p_t(x)`. -/
theorem hasDerivAt_heatKernel_time_eq_laplacian {t : ℝ} (ht : 0 < t) (x : Euc d) :
    HasDerivAt (fun s => heatKernel d s x) (laplacianSum (heatKernel d t) x) t :=
  (hasDerivAt_heatKernel_time ht x).congr_deriv (laplacianSum_heatKernel ht x).symm

end

end LatticeProb.Analysis.Schauder
