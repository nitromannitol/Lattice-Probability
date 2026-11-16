import LatticeProb.Analysis.Schauder.Cutoff
import LatticeProb.Analysis.Schauder.BoundedDerivsCompact
import LatticeProb.Analysis.Schauder.CommutedHeat
import LatticeProb.Analysis.Schauder.DuhamelPower
import LatticeProb.Analysis.Schauder.HeatApproxId
import LatticeProb.Analysis.Schauder.HeatAverageDeriv
import LatticeProb.Analysis.Schauder.HeatEquation
import LatticeProb.Analysis.Schauder.IBPTwice
import LatticeProb.Analysis.Schauder.KernelL1

/-!
# A bound on one second derivative from a bound on the Hölder tail of the Laplacian

Let `u` be a `C²` function whose size is at most `K₀` on the ball of radius `2` around `x₀` and
whose Laplacian is bounded by `K₁` there and is `α`-Hölder with constant `K₁` on that ball. For
every `x` in the unit ball around `x₀` and unit directions `a`, `b`, the second derivative
`∂_a ∂_b u (x)` is bounded by `(2^{d/2} + 1) K₀ + C (K₀ + K₁) / (α / 2)`, where `C` is the
constant of a heat-kernel estimate on the Hölder tail, taken as a hypothesis.

The function `u` is first replaced by `w = χ u` with the cutoff `χ` at `x`; `w` has bounded
derivatives, is bounded by `K₀`, and agrees with `u` near `x` to second order. The proof then
compares `∂_a ∂_b w (x)` with its heat average `Φ(t) = ∫ p_t(y) ∂_a ∂_b w (x - y) dy` at time `1`:

* at time `1`, two integrations by parts move both derivatives onto `p_1`, so `|Φ(1)|` is at most
  `(2^{d/2} + 1) K₀` by the `L¹` bound on `∂_b ∂_a p_1`;
* `Φ(t) → ∂_a ∂_b w (x)` as `t → 0⁺`, and by the heat equation `Φ'(t) = ∫ Δp_t ∂_a ∂_b w (x - ·)`,
  which the commutation of the Laplacian with `∂_a ∂_b` turns into
  `∫ ∂_a ∂_b p_t Δw (x - ·)`; the hypothesis bounds this by `C (K₀ + K₁) t^{α/2 - 1}`, and the
  power-law Duhamel bound gives `|Φ(1) - ∂_a ∂_b w (x)| ≤ C (K₀ + K₁) / (α / 2)`.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- **Entry bound from the Hölder tail of the Laplacian.** Suppose the heat-kernel estimate
`hΨ` holds: for a `C²` function `w` with bounded derivatives, `|w| ≤ K₀`, `|Δw (x)| ≤ K₁` and
`|Δw (x - y) - Δw (x)| ≤ K₁ ‖y‖^α` for `‖y‖ < 1/2`, the integral
`∫ ∂_a ∂_b p_t(y) Δw (x - y) dy` is at most `C (K₀ + K₁) t^{α/2 - 1}` for `0 < t ≤ 1`. Then for a
`C²` function `u` that is bounded by `K₀` on the ball of radius `2` around `x₀` and has a Laplacian
that is bounded by `K₁` and `α`-Hölder with constant `K₁` there, every unit second directional
derivative of `u` at a point of the unit ball around `x₀` is at most
`(2^{d/2} + 1) K₀ + C (K₀ + K₁) / (α / 2)`. -/
theorem abs_dirDeriv_dirDeriv_le_of_psiBound {α : ℝ} (hα0 : 0 < α)
    (h3 : ∀ t : ℝ, 0 < t → ∀ a b c : Euc d,
      Integrable (dirDeriv a (dirDeriv b (dirDeriv c (heatKernel d t)))))
    (h4 : ∀ t : ℝ, 0 < t → ∀ a b c e : Euc d,
      Integrable (dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e (heatKernel d t))))))
    {CΨ : ℝ} (hΨ : ∀ (w : Euc d → ℝ) (x : Euc d) (K₀ K₁ : ℝ), BoundedDerivs 2 w →
      (∀ y, |w y| ≤ K₀) → |laplacianSum w x| ≤ K₁ → 0 ≤ K₁ →
      (∀ y, ‖y‖ < 1 / 2 → |laplacianSum w (x - y) - laplacianSum w x| ≤ K₁ * ‖y‖ ^ α) →
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ a b : Euc d, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
        |∫ y, dirDeriv a (dirDeriv b (heatKernel d t)) y * laplacianSum w (x - y)| ≤
          CΨ * (K₀ + K₁) * t ^ (α / 2 - 1))
    (u : Euc d → ℝ) (x₀ x : Euc d) (K₀ K₁ : ℝ) (hu : ContDiff ℝ 2 u)
    (hx : x ∈ Metric.closedBall x₀ 1) (hu0 : ∀ z ∈ Metric.closedBall x₀ 2, |u z| ≤ K₀)
    (hu1 : ∀ z ∈ Metric.closedBall x₀ 2, ∀ z' ∈ Metric.closedBall x₀ 2,
      |laplacianSum u z| ≤ K₁ ∧ |laplacianSum u z - laplacianSum u z'| ≤ K₁ * dist z z' ^ α)
    (a b : Euc d) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |dirDeriv a (dirDeriv b u) x| ≤
      (2 ^ ((d : ℝ) / 2) + 1) * K₀ + CΨ * (K₀ + K₁) / (α / 2) := by
  -- the localized function
  set w : Euc d → ℝ := fun z => cutoffBump x z * u z with hw_def
  have hw : BoundedDerivs 2 w := boundedDerivs_bump_mul (cutoffBump x) hu
  have hwK : ∀ y, |w y| ≤ K₀ := abs_cutoffBump_mul_le hx hu0
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (hu0 x₀ (Metric.mem_closedBall_self (by norm_num)))
  have hG : BoundedDerivs 0 (dirDeriv a (dirDeriv b w)) := (hw.dirDeriv b).dirDeriv a
  obtain ⟨AG, hAG⟩ := hG.exists_abs_le
  have hGc : Continuous (dirDeriv a (dirDeriv b w)) := hG.continuous
  have hxball : x ∈ Metric.ball x (3 / 4) := Metric.mem_ball_self (by norm_num)
  have hxdist : dist x x₀ ≤ 1 := Metric.mem_closedBall.1 hx
  have hx2 : x ∈ Metric.closedBall x₀ 2 := by
    rw [Metric.mem_closedBall]
    linarith
  have hGx : dirDeriv a (dirDeriv b w) x = dirDeriv a (dirDeriv b u) x :=
    dirDeriv_dirDeriv_cutoffBump_mul hu hxball a b
  have hlapx : laplacianSum w x = laplacianSum u x := laplacianSum_cutoffBump_mul hxball
  have hlapx1 : |laplacianSum u x| ≤ K₁ := (hu1 x hx2 x hx2).1
  have hK₁ : 0 ≤ K₁ := (abs_nonneg _).trans hlapx1
  -- the local Hölder hypothesis for the localized function
  have hholder : ∀ y : Euc d, ‖y‖ < 1 / 2 →
      |laplacianSum w (x - y) - laplacianSum w x| ≤ K₁ * ‖y‖ ^ α := by
    intro y hy
    have hdist : dist (x - y) x = ‖y‖ := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    have hball : x - y ∈ Metric.ball x (3 / 4) := by
      rw [Metric.mem_ball, hdist]
      linarith
    have hmem : x - y ∈ Metric.closedBall x₀ 2 := by
      rw [Metric.mem_closedBall]
      calc dist (x - y) x₀ ≤ dist (x - y) x + dist x x₀ := dist_triangle _ _ _
        _ ≤ 2 := by rw [hdist]; linarith
    have := (hu1 (x - y) hmem x hx2).2
    rw [hdist] at this
    rw [laplacianSum_cutoffBump_mul hball, hlapx]
    exact this
  -- the bound on `Φ'`
  have hΦ'eq : ∀ t : ℝ, 0 < t →
      ∫ y, ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) *
          dirDeriv a (dirDeriv b w) (x - y) =
        ∫ y, dirDeriv a (dirDeriv b (heatKernel d t)) y * laplacianSum w (x - y) := by
    intro t ht
    rw [← integral_laplacianSum_heatKernel_mul_comp_sub ht hw (h3 t ht) (h4 t ht) x a b]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [laplacianSum_heatKernel ht y]
  have hΦ' : ∀ t : ℝ, 0 < t → t ≤ 1 →
      |∫ y, ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) *
          dirDeriv a (dirDeriv b w) (x - y)| ≤ CΨ * (K₀ + K₁) * t ^ (α / 2 - 1) := by
    intro t ht ht1
    rw [hΦ'eq t ht]
    exact hΨ w x K₀ K₁ hw hwK (hlapx ▸ hlapx1) hK₁ hholder t ht ht1 a b ha hb
  -- Duhamel
  have hD := abs_sub_le_of_hasDerivAt_le_rpow (half_pos hα0)
    (Φ := fun t => ∫ y, heatKernel d t y * dirDeriv a (dirDeriv b w) (x - y))
    (Φ' := fun t => ∫ y, ((-(d : ℝ) / (2 * t) + ‖y‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t y) *
      dirDeriv a (dirDeriv b w) (x - y))
    (L := dirDeriv a (dirDeriv b w) x) (c := CΨ * (K₀ + K₁))
    (fun t ht => hasDerivAt_integral_heatKernel_mul hGc hAG x ht) hΦ'
    (tendsto_integral_heatKernel_mul hGc hAG x)
  -- the value at time `1`
  have hK : ContDiff ℝ 2 (heatKernel d 1) := (contDiff_heatKernel 1).of_le (by simp)
  have h1 : |∫ y, heatKernel d 1 y * dirDeriv a (dirDeriv b w) (x - y)| ≤
      (2 ^ ((d : ℝ) / 2) + 1) * K₀ := by
    rw [integral_mul_dirDeriv_dirDeriv_comp_sub hK (integrable_heatKernel one_pos)
      (integrable_dirDeriv_heatKernel one_pos)
      (fun e e' => integrable_dirDeriv_dirDeriv_heatKernel one_pos e e') hw x a b]
    have hint : Integrable fun y => K₀ * |dirDeriv b (dirDeriv a (heatKernel d 1)) y| :=
      (integrable_dirDeriv_dirDeriv_heatKernel one_pos a b).abs.const_mul K₀
    have h2 : |∫ y, dirDeriv b (dirDeriv a (heatKernel d 1)) y * w (x - y)| ≤
        ∫ y, K₀ * |dirDeriv b (dirDeriv a (heatKernel d 1)) y| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |dirDeriv b (dirDeriv a (heatKernel d 1)) y| * |w (x - y)|
          ≤ |dirDeriv b (dirDeriv a (heatKernel d 1)) y| * K₀ := by
            gcongr
            exact hwK (x - y)
        _ = K₀ * |dirDeriv b (dirDeriv a (heatKernel d 1)) y| := mul_comm _ _
    have h3' := integral_abs_dirDeriv_dirDeriv_heatKernel_le (d := d) one_pos a b
    have hab : ‖a‖ * ‖b‖ ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.2 ha) (norm_nonneg b)]
    calc |∫ y, dirDeriv b (dirDeriv a (heatKernel d 1)) y * w (x - y)|
        ≤ ∫ y, K₀ * |dirDeriv b (dirDeriv a (heatKernel d 1)) y| := h2
      _ = K₀ * ∫ y, |dirDeriv b (dirDeriv a (heatKernel d 1)) y| := integral_const_mul _ _
      _ ≤ K₀ * ((2 ^ ((d : ℝ) / 2) + 1) * ‖a‖ * ‖b‖ / 1) := by gcongr
      _ = K₀ * ((2 ^ ((d : ℝ) / 2) + 1) * (‖a‖ * ‖b‖)) := by ring
      _ ≤ K₀ * ((2 ^ ((d : ℝ) / 2) + 1) * 1) := by gcongr
      _ = (2 ^ ((d : ℝ) / 2) + 1) * K₀ := by ring
  have h5 := abs_sub_abs_le_abs_sub (dirDeriv a (dirDeriv b w) x)
    (∫ y, heatKernel d 1 y * dirDeriv a (dirDeriv b w) (x - y))
  rw [abs_sub_comm] at h5
  beta_reduce at hD
  rw [hGx] at h5 hD
  linarith

end

end LatticeProb.Analysis.Schauder
