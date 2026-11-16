import LatticeProb.Analysis.Schauder.Split
import LatticeProb.Analysis.Schauder.InnerBound
import LatticeProb.Analysis.Schauder.OuterBound
import LatticeProb.Analysis.Schauder.KernelTail
import LatticeProb.Analysis.Schauder.HolderMoment
import LatticeProb.Analysis.Schauder.KernelMeanZero
import LatticeProb.Analysis.Schauder.KernelL1
import LatticeProb.Analysis.Schauder.KernelIntegral
import LatticeProb.Analysis.Schauder.KernelDerivSpace
import LatticeProb.Analysis.Schauder.BoundedDerivs
import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
# Convolving a second derivative of the heat kernel with a Hölder Laplacian

Let `w` be a `C²` function with bounded derivatives, `|w| ≤ K₀`, whose Laplacian `Δw` is bounded
by `K₁` at `x` and Hölder continuous of exponent `α ∈ [0, 1]` at `x` with constant `K₁` on the ball
of radius `1/2`. For a second derivative `K = ∂_a ∂_b p_t` of the heat kernel with unit-bounded
directions and `0 < t ≤ 1`, the convolution `∫ K(y) Δw(x - y) dy` is bounded by
`CΨ (K₀ + K₁) t^{α/2 - 1}`, with `CΨ` independent of `w`, `x`, `t`, `a` and `b`.

The kernel `K` is integrable with mean zero, so it is split with the bump `χ` that equals `1` on
the ball of radius `1/4` and vanishes outside the ball of radius `1/2` (`Split.lean`) into

* a near part `∫ χ K (Δw(x - ·) - Δw(x))`, bounded by `K₁ ∫ H` for the dominating profile
  `H = 32 · 2^{d/2} t^{α/2 - 1} p_{2t}` coming from the Hölder moment of `K` (`InnerBound.lean`);
* a far part `∫ (1 - χ) K Δw(x - ·)`, in which two integrations by parts move the Laplacian onto
  `(1 - χ) K`; away from the origin the derivatives of `K` up to order two are dominated by
  `M p_{4t}`, and the bound is `C M K₀ ∫ p_{4t}` (`OuterBound.lean`);
* a correction `Δw(x) ∫ (1 - χ) K`, bounded by `K₁ M ∫ p_{4t}`.

Since `∫ p_s = 1` and `t^{α/2 - 1} ≥ 1` for `t ≤ 1`, the three bounds add up to the claim.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The bump at the origin that separates the near and far parts of the kernel. -/
def splitBump : ContDiffBump (0 : Euc d) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The inner radius of `splitBump` is `1/4`. -/
theorem splitBump_rIn : (splitBump : ContDiffBump (0 : Euc d)).rIn = 1 / 4 := rfl

/-- The outer radius of `splitBump` is `1/2`. -/
theorem splitBump_rOut : (splitBump : ContDiffBump (0 : Euc d)).rOut = 1 / 2 := rfl

/-- The Laplacian of a function with two bounded derivatives is continuous and bounded: it is the
sum of the pure second derivatives, each of which has bounded derivatives of order zero. -/
theorem continuous_and_exists_abs_le_laplacianSum {w : Euc d → ℝ} (hw : BoundedDerivs 2 w) :
    Continuous (laplacianSum w) ∧ ∃ B : ℝ, ∀ y, |laplacianSum w y| ≤ B := by
  have hfun : laplacianSum w = fun z => ∑ i : Fin d, dirDeriv (EuclideanSpace.single i 1)
      (dirDeriv (EuclideanSpace.single i 1) w) z :=
    funext (laplacianSum_eq_sum_dirDeriv_of_contDiff hw.1)
  have hi : ∀ i : Fin d, BoundedDerivs 0 (dirDeriv (EuclideanSpace.single i 1)
      (dirDeriv (EuclideanSpace.single i 1) w)) := fun i =>
    (hw.dirDeriv (EuclideanSpace.single i 1)).dirDeriv (EuclideanSpace.single i 1)
  choose B hB using fun i => (hi i).exists_abs_le
  refine ⟨?_, ∑ i, B i, fun y => ?_⟩
  · rw [hfun]
    exact continuous_finsetSum _ fun i _ => (hi i).continuous
  · rw [hfun]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB i y)

/-- The arithmetic of the three bounds: if the near part, the far part and the correction satisfy
the three estimates, their combination `I₁ + I₂ - g I₃` is at most `(P + Q + R) (K₀ + K₁) L` once
`L ≥ 1`. -/
theorem abs_add_sub_mul_le_of_bounds {I₁ I₂ I₃ g K₀ K₁ P Q R L : ℝ}
    (hI₁ : |I₁| ≤ K₁ * (P * L)) (hI₂ : |I₂| ≤ Q * K₀ * 1) (hI₃ : |I₃| ≤ R * 1)
    (hg : |g| ≤ K₁) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hL : 1 ≤ L) : |I₁ + I₂ - g * I₃| ≤ (P + Q + R) * (K₀ + K₁) * L := by
  have h1 : |I₁ + I₂ - g * I₃| ≤ |I₁| + |I₂| + |g| * |I₃| :=
    calc |I₁ + I₂ - g * I₃| ≤ |I₁ + I₂| + |g * I₃| := abs_sub _ _
      _ ≤ |I₁| + |I₂| + |g| * |I₃| := by
        rw [abs_mul]
        exact add_le_add_left (abs_add_le _ _) _
  have h2 : |g| * |I₃| ≤ K₁ * (R * 1) := mul_le_mul hg hI₃ (abs_nonneg _) hK₁
  have hL0 : 0 ≤ L - 1 := sub_nonneg.2 hL
  have h3 : 0 ≤ (L - 1) * (Q * K₀) := mul_nonneg hL0 (mul_nonneg hQ hK₀)
  have h4 : 0 ≤ (L - 1) * (R * K₁) := mul_nonneg hL0 (mul_nonneg hR hK₁)
  have hL' : 0 ≤ L := zero_le_one.trans hL
  have h5 : 0 ≤ P * K₀ * L := mul_nonneg (mul_nonneg hP hK₀) hL'
  have h6 : 0 ≤ Q * K₁ * L := mul_nonneg (mul_nonneg hQ hK₁) hL'
  have h7 : 0 ≤ R * K₀ * L := mul_nonneg (mul_nonneg hR hK₀) hL'
  have h8 : 0 ≤ R * K₁ * L := mul_nonneg (mul_nonneg hR hK₁) hL'
  linarith [h1, h2, h3, h4, h5, h6, h7, h8]

/-- **Convolution of a second derivative of the heat kernel with a Hölder Laplacian.** If `w` is
`C²` with bounded derivatives, `|w| ≤ K₀`, `|Δw(x)| ≤ K₁`, and `Δw` is `α`-Hölder at `x` with
constant `K₁` on the ball of radius `1/2`, then for `0 < t ≤ 1` and unit-bounded directions `a`,
`b` the integral `∫ ∂_a ∂_b p_t(y) Δw(x - y) dy` is at most `CΨ (K₀ + K₁) t^{α/2 - 1}` in absolute
value, where `CΨ` depends only on the dimension and on `α`. -/
theorem exists_abs_integral_dirDeriv_dirDeriv_heatKernel_mul_le {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ (w : Euc d → ℝ) (x : Euc d) (K₀ K₁ : ℝ), BoundedDerivs 2 w →
      (∀ y, |w y| ≤ K₀) → |laplacianSum w x| ≤ K₁ → 0 ≤ K₁ →
      (∀ y, ‖y‖ < 1 / 2 → |laplacianSum w (x - y) - laplacianSum w x| ≤ K₁ * ‖y‖ ^ α) →
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ a b : Euc d, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        |∫ y, dirDeriv a (dirDeriv b (heatKernel d t)) y * laplacianSum w (x - y)| ≤
          CΨ * (K₀ + K₁) * t ^ (α / 2 - 1) := by
  obtain ⟨Co, hCo0, hCo⟩ :=
    exists_abs_integral_one_sub_bump_mul_laplacianSum_le (splitBump : ContDiffBump (0 : Euc d))
  obtain ⟨M, hM0, hM⟩ := exists_heatKernel_chain_tail (d := d) (δ := 1 / 4) (by norm_num)
  refine ⟨32 * 2 ^ ((d : ℝ) / 2) + Co * M + M, by positivity, ?_⟩
  intro w x K₀ K₁ hw hwK₀ hgx hK₁ hHold t ht ht1 a b ha hb
  obtain ⟨hgc, B, hB⟩ := continuous_and_exists_abs_le_laplacianSum hw
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (hwK₀ 0)
  -- the kernel is smooth, integrable and has mean zero
  have hs : ContDiff ℝ (⊤ : ℕ∞) (heatKernel d t) := (contDiff_heatKernel t).of_le le_top
  have hKs : ContDiff ℝ (⊤ : ℕ∞) (dirDeriv a (dirDeriv b (heatKernel d t))) :=
    contDiff_dirDeriv (contDiff_dirDeriv hs b) a
  have hK2 : ContDiff ℝ 2 (dirDeriv a (dirDeriv b (heatKernel d t))) :=
    hKs.of_le (WithTop.coe_le_coe.2 le_top)
  have hKint : Integrable (dirDeriv a (dirDeriv b (heatKernel d t))) :=
    integrable_dirDeriv_dirDeriv_heatKernel ht b a
  have hK0 : ∫ y, dirDeriv a (dirDeriv b (heatKernel d t)) y = 0 :=
    integral_dirDeriv_dirDeriv_heatKernel ht a b
  have hsplit := integral_mul_comp_sub_eq_split (splitBump : ContDiffBump (0 : Euc d)) hKint hK0
    hgc hB x
  -- the near part
  have hH : Integrable fun y =>
      32 * 2 ^ ((d : ℝ) / 2) * t ^ (α / 2 - 1) * heatKernel d (2 * t) y :=
    (integrable_heatKernel (by positivity)).const_mul _
  have hHint : ∫ y, 32 * 2 ^ ((d : ℝ) / 2) * t ^ (α / 2 - 1) * heatKernel d (2 * t) y =
      32 * 2 ^ ((d : ℝ) / 2) * t ^ (α / 2 - 1) := by
    rw [integral_const_mul, integral_heatKernel (by positivity), mul_one]
  have hnear := abs_integral_bump_mul_sub_le (splitBump : ContDiffBump (0 : Euc d))
    hKs.continuous hgc hH
    (fun y => abs_dirDeriv_dirDeriv_heatKernel_mul_rpow_le ht hα0 hα1 ha hb y) hK₁
    (fun y hy => hHold y hy)
  rw [hHint] at hnear
  -- the far part and the correction
  obtain ⟨htail0, htail1, htail2⟩ := hM t ht a b ha hb
  have hG : Integrable (heatKernel d (4 * t)) := integrable_heatKernel (by positivity)
  have hG0 : ∀ y, 0 ≤ heatKernel d (4 * t) y := fun y => heatKernel_nonneg (by positivity) y
  have hGint : ∫ y, heatKernel d (4 * t) y = 1 := integral_heatKernel (by positivity)
  have hfar := hCo (dirDeriv a (dirDeriv b (heatKernel d t))) (heatKernel d (4 * t)) w M K₀ hK2
    hG hG0 hM0 htail0 htail1 htail2 hw hwK₀ x
  have hcorr := abs_integral_one_sub_bump_mul_le (splitBump : ContDiffBump (0 : Euc d))
    hG hG0 hM0 htail0
  rw [hGint] at hfar hcorr
  have hL : 1 ≤ t ^ (α / 2 - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  rw [hsplit]
  exact abs_add_sub_mul_le_of_bounds hnear hfar hcorr hgx hK₀ hK₁ (by positivity)
    (mul_nonneg hCo0 hM0) hM0 hL

end

end LatticeProb.Analysis.Schauder
