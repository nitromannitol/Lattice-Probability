import LatticeProb.Analysis.Schauder.HeatApproxId
import LatticeProb.Analysis.Schauder.HeatAverageDeriv
import LatticeProb.Analysis.Schauder.HeatEquation
import LatticeProb.Analysis.Schauder.KernelL1
import LatticeProb.Analysis.Schauder.IBPTwice
import LatticeProb.Analysis.Schauder.IBPLaplacian
import LatticeProb.Analysis.Schauder.DuhamelBound
import LatticeProb.Analysis.Schauder.BoundedDerivs
import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.Heat.HessianEntryBound`.

# The Schauder-free bound on one second derivative

For a `C⁴` function `v` with bounded derivatives, `|v| ≤ A` and `‖∇Δv‖ ≤ B`, every unit second
directional derivative `∂_u ∂_w v` is bounded by `(2^{d/2} + 1) A + 2 · 2^{d/2} B`. The proof
compares `∂_u ∂_w v` with its heat average `Φ(t) = ∫ p_t(y) ∂_u ∂_w v(x - y) dy` at time `1`:

* at time `1`, two integrations by parts move both derivatives onto `p_1`, so `|Φ(1)|` is at most
  `(2^{d/2} + 1) A` by the `L¹` bound on `∂_w ∂_u p_1`;
* `Φ(t) → ∂_u ∂_w v(x)` as `t → 0⁺`, and by the heat equation `Φ'(t) = ∫ Δp_t ∂_u ∂_w v(x - ·)`,
  which two integrations by parts turn into `∫ ∂_u p_t ∂_w Δv(x - ·)`, of size at most
  `2^{d/2} B / √t`; the Duhamel bound then gives `|Φ(1) - ∂_u ∂_w v(x)| ≤ 2 · 2^{d/2} B`.

No Schauder estimate and no Hölder norm enter.
-/

namespace LatticeProb.Analysis.Schauder

open Real MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- The time derivative of a heat-kernel average is the average of `Δ p_t`, written as the sum of
the pure second derivatives of `p_t`. -/
private theorem integral_coeff_heatKernel_mul_eq {t : ℝ} (ht : 0 < t) {g : Euc d → ℝ}
    (hgc : Continuous g) {A : ℝ} (hgA : ∀ y, |g y| ≤ A) (x : Euc d) :
    ∫ y, ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) * g (x - y) =
      ∑ i : Fin d, ∫ y, dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) (heatKernel d t)) y * g (x - y) := by
  have hgx : Continuous fun y : Euc d => g (x - y) :=
    hgc.comp (continuous_const.sub continuous_id)
  have hK : ContDiff ℝ 2 (heatKernel d t) := (contDiff_heatKernel t).of_le (by simp)
  have hpt : ∀ y : Euc d, (-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y =
      ∑ i : Fin d, dirDeriv (EuclideanSpace.single i 1)
        (dirDeriv (EuclideanSpace.single i 1) (heatKernel d t)) y := fun y =>
    (laplacianSum_heatKernel ht y).symm.trans (laplacianSum_eq_sum_dirDeriv_of_contDiff hK y)
  simp_rw [hpt, Finset.sum_mul]
  refine integral_finsetSum _ fun i _ => ?_
  exact (integrable_dirDeriv_dirDeriv_heatKernel ht _ _).mul_bdd hgx.aestronglyMeasurable
    (Eventually.of_forall fun y => hgA (x - y))

/-- **Schauder-free bound on one second derivative.** If `v` is `C⁴` with bounded derivatives,
`|v| ≤ A` and `‖∇Δv‖ ≤ B`, then every unit second directional derivative of `v` is at most
`(2^{d/2} + 1) A + 2 · 2^{d/2} B`. Proof by the heat semigroup (Duhamel). -/
theorem abs_dirDeriv_dirDeriv_le_of_bounded {v : Euc d → ℝ} {A B : ℝ} (hv : BoundedDerivs 4 v)
    (hvA : ∀ y, |v y| ≤ A) (hvB : ∀ y, ‖fderiv ℝ (laplacianSum v) y‖ ≤ B)
    (x u w : Euc d) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |dirDeriv u (dirDeriv w v) x| ≤
      (2 ^ ((d : ℝ) / 2) + 1) * A + 2 * (2 ^ ((d : ℝ) / 2) * B) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hvA x)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hvB x)
  have hc : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  have hG : BoundedDerivs 2 (dirDeriv u (dirDeriv w v)) := (hv.dirDeriv w).dirDeriv u
  obtain ⟨AG, hAG⟩ := hG.exists_abs_le
  have hGc : Continuous (dirDeriv u (dirDeriv w v)) := hG.continuous
  have hK : ContDiff ℝ 2 (heatKernel d 1) := (contDiff_heatKernel 1).of_le (by simp)
  -- the bound on `Φ'`
  have hΦ' : ∀ t : ℝ, 0 < t → t ≤ 1 →
      |∫ y, ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) *
          dirDeriv u (dirDeriv w v) (x - y)| ≤ 2 ^ ((d : ℝ) / 2) * B / Real.sqrt t := by
    intro t ht ht1
    have hK_t : ContDiff ℝ 2 (heatKernel d t) := (contDiff_heatKernel t).of_le (by simp)
    rw [integral_coeff_heatKernel_mul_eq ht hGc hAG x,
      sum_integral_laplacian_kernel_mul_comp_sub hK_t (integrable_heatKernel ht)
        (integrable_dirDeriv_heatKernel ht)
        (fun e e' => integrable_dirDeriv_dirDeriv_heatKernel ht e e') hv x u w]
    have hpt : ∀ z : Euc d, |dirDeriv w (laplacianSum v) z| ≤ B := by
      intro z
      have h1 : |dirDeriv w (laplacianSum v) z| ≤ ‖fderiv ℝ (laplacianSum v) z‖ * ‖w‖ := by
        have := ContinuousLinearMap.le_opNorm (fderiv ℝ (laplacianSum v) z) w
        rwa [← Real.norm_eq_abs]
      calc |dirDeriv w (laplacianSum v) z|
          ≤ ‖fderiv ℝ (laplacianSum v) z‖ * ‖w‖ := h1
        _ ≤ ‖fderiv ℝ (laplacianSum v) z‖ * 1 := by gcongr
        _ ≤ B := by rw [mul_one]; exact hvB z
    have hint : Integrable fun y => B * |dirDeriv u (heatKernel d t) y| :=
      (integrable_dirDeriv_heatKernel ht u).abs.const_mul B
    have h1 : |∫ y, dirDeriv u (heatKernel d t) y * dirDeriv w (laplacianSum v) (x - y)| ≤
        ∫ y, B * |dirDeriv u (heatKernel d t) y| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |dirDeriv u (heatKernel d t) y| * |dirDeriv w (laplacianSum v) (x - y)|
          ≤ |dirDeriv u (heatKernel d t) y| * B := by
            gcongr
            exact hpt (x - y)
        _ = B * |dirDeriv u (heatKernel d t) y| := mul_comm _ _
    have h2 := integral_abs_dirDeriv_heatKernel_le ht u
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    calc |∫ y, dirDeriv u (heatKernel d t) y * dirDeriv w (laplacianSum v) (x - y)|
        ≤ ∫ y, B * |dirDeriv u (heatKernel d t) y| := h1
      _ = B * ∫ y, |dirDeriv u (heatKernel d t) y| := integral_const_mul _ _
      _ ≤ B * (2 ^ ((d : ℝ) / 2) * ‖u‖ / Real.sqrt t) := by gcongr
      _ ≤ B * (2 ^ ((d : ℝ) / 2) * 1 / Real.sqrt t) := by gcongr
      _ = 2 ^ ((d : ℝ) / 2) * B / Real.sqrt t := by ring
  -- Duhamel
  have hD := abs_sub_le_of_hasDerivAt_le_div_sqrt
    (Φ := fun t => ∫ y, heatKernel d t y * dirDeriv u (dirDeriv w v) (x - y))
    (Φ' := fun t => ∫ y, ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) *
      dirDeriv u (dirDeriv w v) (x - y))
    (L := dirDeriv u (dirDeriv w v) x) (c := 2 ^ ((d : ℝ) / 2) * B)
    (fun t ht => hasDerivAt_integral_heatKernel_mul hGc hAG x ht) hΦ'
    (tendsto_integral_heatKernel_mul hGc hAG x)
  -- the value at time `1`
  have h1 : |∫ y, heatKernel d 1 y * dirDeriv u (dirDeriv w v) (x - y)| ≤
      (2 ^ ((d : ℝ) / 2) + 1) * A := by
    rw [integral_mul_dirDeriv_dirDeriv_comp_sub hK (integrable_heatKernel one_pos)
      (integrable_dirDeriv_heatKernel one_pos)
      (fun e e' => integrable_dirDeriv_dirDeriv_heatKernel one_pos e e')
      (hv.mono (by norm_num : 2 ≤ 4)) x u w]
    have hint : Integrable fun y => A * |dirDeriv w (dirDeriv u (heatKernel d 1)) y| :=
      (integrable_dirDeriv_dirDeriv_heatKernel one_pos u w).abs.const_mul A
    have h2 : |∫ y, dirDeriv w (dirDeriv u (heatKernel d 1)) y * v (x - y)| ≤
        ∫ y, A * |dirDeriv w (dirDeriv u (heatKernel d 1)) y| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |dirDeriv w (dirDeriv u (heatKernel d 1)) y| * |v (x - y)|
          ≤ |dirDeriv w (dirDeriv u (heatKernel d 1)) y| * A := by
            gcongr
            exact hvA (x - y)
        _ = A * |dirDeriv w (dirDeriv u (heatKernel d 1)) y| := mul_comm _ _
    have h3 := integral_abs_dirDeriv_dirDeriv_heatKernel_le (d := d) one_pos u w
    have hu1 : ‖u‖ * ‖w‖ ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.2 hu) (norm_nonneg w)]
    calc |∫ y, dirDeriv w (dirDeriv u (heatKernel d 1)) y * v (x - y)|
        ≤ ∫ y, A * |dirDeriv w (dirDeriv u (heatKernel d 1)) y| := h2
      _ = A * ∫ y, |dirDeriv w (dirDeriv u (heatKernel d 1)) y| := integral_const_mul _ _
      _ ≤ A * ((2 ^ ((d : ℝ) / 2) + 1) * ‖u‖ * ‖w‖ / 1) := by gcongr
      _ = A * ((2 ^ ((d : ℝ) / 2) + 1) * (‖u‖ * ‖w‖)) := by ring
      _ ≤ A * ((2 ^ ((d : ℝ) / 2) + 1) * 1) := by gcongr
      _ = (2 ^ ((d : ℝ) / 2) + 1) * A := by ring
  have h4 := abs_sub_abs_le_abs_sub (dirDeriv u (dirDeriv w v) x)
    (∫ y, heatKernel d 1 y * dirDeriv u (dirDeriv w v) (x - y))
  rw [abs_sub_comm] at h4
  beta_reduce at hD
  linarith

end

end LatticeProb.Analysis.Schauder
