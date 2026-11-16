import LatticeProb.Analysis.Schauder.IBPKernel
import LatticeProb.Analysis.Schauder.BoundedDerivs
import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.Heat.IBPLaplacian`.

# Moving the Laplacian onto an integrable kernel

Integrating by parts four times moves the pure second derivatives of a `C⁴` function `v` with
bounded derivatives onto an integrable `C²` kernel `K`: for a fixed direction `e`,
`∫ ∂_e∂_e K(y) ∂_u∂_w v(x - y) dy = ∫ ∂_u K(y) ∂_e∂_e∂_w v(x - y) dy`.
Summing over the coordinate directions turns the left side into the Laplacian of `K` and the
right side into `∂_w` of the Laplacian of `v`:
`Σ_i ∫ ∂_i²K(y) ∂_u∂_w v(x - y) dy = ∫ ∂_u K(y) ∂_w Δv(x - y) dy`.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Integration by parts for the Laplacian of a kernel against a second derivative:
`Σ_i ∫ ∂_i²K(y) ∂_u∂_w v(x − y) dy = ∫ ∂_u K(y) ∂_w Δv(x − y) dy`. Integrability of `K`
itself is not used, only that of its first and second derivatives. -/
theorem sum_integral_laplacian_kernel_mul_comp_sub {K v : Euc d → ℝ}
    (hK : ContDiff ℝ 2 K) (_hK0 : Integrable K) (hK1 : ∀ e : Euc d, Integrable (dirDeriv e K))
    (hK2 : ∀ e e' : Euc d, Integrable (dirDeriv e' (dirDeriv e K)))
    (hv : BoundedDerivs 4 v) (x u w : Euc d) :
    ∑ i : Fin d, ∫ y, dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) K) y * dirDeriv u (dirDeriv w v) (x - y) =
      ∫ y, dirDeriv u K y * dirDeriv w (laplacianSum v) (x - y) := by
  have hsub : Continuous fun y : Euc d => x - y := continuous_const.sub continuous_id
  have hf3 : BoundedDerivs 3 (dirDeriv w v) := hv.dirDeriv w
  have hf2 : ContDiff ℝ 2 (dirDeriv w v) := by
    have := (hf3.mono (by norm_num : 2 ≤ 3)).1
    exact_mod_cast this
  have hKdiff : ∀ e : Euc d, Differentiable ℝ (dirDeriv e K) := fun e =>
    ((hK.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  -- the per-direction identity
  have key : ∀ e : Euc d,
      ∫ y, dirDeriv e (dirDeriv e K) y * dirDeriv u (dirDeriv w v) (x - y) =
        ∫ y, dirDeriv u K y * dirDeriv e (dirDeriv e (dirDeriv w v)) (x - y) := by
    intro e
    have hG : BoundedDerivs 2 (dirDeriv u (dirDeriv w v)) := hf3.dirDeriv u
    have hH : BoundedDerivs 2 (dirDeriv e (dirDeriv w v)) := hf3.dirDeriv e
    obtain ⟨AG, hAG⟩ := hG.exists_abs_le
    obtain ⟨BG, hBG⟩ := hG.exists_norm_fderiv_le
    obtain ⟨AH, hAH⟩ := hH.exists_abs_le
    obtain ⟨BH, hBH⟩ := hH.exists_norm_fderiv_le
    -- (a) move `∂_e` from the kernel `∂_e K` onto `G = ∂_u ∂_w v`
    have ha : ∫ y, dirDeriv e (dirDeriv e K) y * dirDeriv u (dirDeriv w v) (x - y) =
        ∫ y, dirDeriv e K y * dirDeriv e (dirDeriv u (dirDeriv w v)) (x - y) :=
      (integral_mul_fderiv_comp_sub_eq (hKdiff e) (hK1 e) (fun e' => hK2 e e')
        hG.differentiable hG.continuous hG.continuous_fderiv hAG hBG x e).symm
    -- (b) commute `∂_e` and `∂_u` on `∂_w v`
    have hb : dirDeriv e (dirDeriv u (dirDeriv w v)) =
        dirDeriv u (dirDeriv e (dirDeriv w v)) := dirDeriv_comm hf2 e u
    -- (c) move `∂_u` from `H = ∂_e ∂_w v` onto the kernel `∂_e K`
    have hc : ∫ y, dirDeriv e K y * dirDeriv u (dirDeriv e (dirDeriv w v)) (x - y) =
        ∫ y, dirDeriv u (dirDeriv e K) y * dirDeriv e (dirDeriv w v) (x - y) :=
      integral_mul_fderiv_comp_sub_eq (hKdiff e) (hK1 e) (fun e' => hK2 e e')
        hH.differentiable hH.continuous hH.continuous_fderiv hAH hBH x u
    -- (d) commute `∂_u` and `∂_e` on `K`, then move `∂_e` back from the kernel onto `H`
    have hd : dirDeriv u (dirDeriv e K) = dirDeriv e (dirDeriv u K) := dirDeriv_comm hK u e
    have hd' : ∫ y, dirDeriv u K y * dirDeriv e (dirDeriv e (dirDeriv w v)) (x - y) =
        ∫ y, dirDeriv e (dirDeriv u K) y * dirDeriv e (dirDeriv w v) (x - y) :=
      integral_mul_fderiv_comp_sub_eq (hKdiff u) (hK1 u) (fun e' => hK2 u e')
        hH.differentiable hH.continuous hH.continuous_fderiv hAH hBH x e
    rw [ha, hb, hc, hd]
    exact hd'.symm
  -- sum over the coordinate directions
  have hint : ∀ i : Fin d, Integrable (fun y => dirDeriv u K y *
      dirDeriv (EuclideanSpace.single i 1) (dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv w v)) (x - y)) := by
    intro i
    have h1 : BoundedDerivs 1 (dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) (dirDeriv w v))) :=
      (hf3.dirDeriv (EuclideanSpace.single i 1)).dirDeriv (EuclideanSpace.single i 1)
    obtain ⟨A, hA⟩ := h1.exists_abs_le
    exact (hK1 u).mul_bdd (h1.continuous.comp hsub).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hA (x - y))
  have hv3 : ContDiff ℝ 3 v := by
    have := (hv.mono (by norm_num : 3 ≤ 4)).1
    exact_mod_cast this
  simp_rw [key]
  rw [← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [← Finset.mul_sum, dirDeriv_laplacianSum hv3 w (x - y)]

end

end LatticeProb.Analysis.Schauder
