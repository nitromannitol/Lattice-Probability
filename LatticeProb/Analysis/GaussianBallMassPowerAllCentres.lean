import LatticeProb.Analysis.GaussianBallMassPower

/-!
# Gaussian heat bounds at every start for a density restricted to a ball

Let `g ≥ 0` be a density on `ℂ` whose integrals over the balls `B(c, r)`, with centre `c` in the closed
ball `B̄(x₀, R)` and radius `0 < r ≤ 1`, are at most `A r^β`. The restriction `1_{B(x₀, R)} g` then
has ball integrals at most `A' r^{β'}` at every centre of `B̄(x₀, R)` and every radius
(`exists_setLIntegral_ball_indicator_le`). This file removes the restriction on the centre: a ball
`B(z, r)` whose centre lies outside `B̄(x₀, R)` meets `B(x₀, R)` only inside the ball of radius `2r`
around the radial projection of `z` onto `B̄(x₀, R)` (`exists_mem_closedBall_ball_inter_subset`), so
the bound holds at every centre with the constant doubled
(`setLIntegral_ball_indicator_le_of_forall_mem_closedBall`). Consequently the planar Gaussian
averages of `1_{B(x₀, R)} g` with mean `z` over the variances `s ∈ (0, t]` are bounded by
`C t^{β'/2}` uniformly over all starts `z ∈ ℂ`
(`exists_lintegral_Ioc_lintegral_map_prod_gaussianReal_indicator_le_forall`). With the variance
`s` read as Brownian time, this bounds the Green potential `∫_0^t ∫ p_s(z, y) 1_{B(x₀,R)}(y) g(y) dy ds`
of the killed-in-time heat kernel uniformly in the starting point.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

/-- **A ball centred outside a closed ball meets the open ball only near the boundary.** For
`R ≥ 0`, every ball `B(z, r)` satisfies `B(z, r) ∩ B(x₀, R) ⊆ B(z', 2r)` for some centre
`z' ∈ B̄(x₀, R)`: take `z' = z` if `z ∈ B̄(x₀, R)`, and otherwise the radial projection
`z' = x₀ + (R / |z - x₀|) (z - x₀)`. -/
theorem exists_mem_closedBall_ball_inter_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x₀ z : E) {R : ℝ} (hR : 0 ≤ R) (r : ℝ) :
    ∃ z' ∈ closedBall x₀ R, ball z r ∩ ball x₀ R ⊆ ball z' (2 * r) := by
  by_cases hz : z ∈ closedBall x₀ R
  · refine ⟨z, hz, fun y hy => ?_⟩
    have h1 := hy.1
    rw [mem_ball] at h1 ⊢
    linarith [dist_nonneg (x := y) (y := z)]
  · have hd : R < dist z x₀ := not_le.1 hz
    have hd0 : 0 < dist z x₀ := lt_of_le_of_lt hR hd
    refine ⟨x₀ + (R / dist z x₀) • (z - x₀), ?_, fun y hy => ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (div_nonneg hR hd0.le), ← dist_eq_norm, div_mul_cancel₀ R hd0.ne']
    · obtain ⟨hy1, hy2⟩ := hy
      rw [mem_ball] at hy1 hy2 ⊢
      have hzz' : dist z (x₀ + (R / dist z x₀) • (z - x₀)) = dist z x₀ - R := by
        have he : z - (x₀ + (R / dist z x₀) • (z - x₀)) = (1 - R / dist z x₀) • (z - x₀) := by
          rw [sub_smul, one_smul]
          abel
        have hc : 0 ≤ 1 - R / dist z x₀ := by
          rw [sub_nonneg, div_le_one hd0]
          exact hd.le
        rw [dist_eq_norm, he, norm_smul, Real.norm_of_nonneg hc, ← dist_eq_norm, sub_mul, one_mul,
          div_mul_cancel₀ R hd0.ne']
      have htri := dist_triangle y z (x₀ + (R / dist z x₀) • (z - x₀))
      have h3 : dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle z y x₀
      rw [dist_comm z y] at h3
      linarith

/-- **Ball bounds at every centre for a density restricted to a ball.** If `1_{B(x₀, R)} g` has
integrals at most `A r^β` over the balls centred in `B̄(x₀, R)`, with `0 ≤ A` and `β ≤ 1`, then it has
integrals at most `2 A r^β` over every ball. -/
theorem setLIntegral_ball_indicator_le_of_forall_mem_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) (g : E → ℝ≥0∞)
    (x₀ : E) {R A β : ℝ} (hA : 0 ≤ A) (hβ1 : β ≤ 1)
    (h : ∀ z ∈ closedBall x₀ R, ∀ r, 0 < r →
      ∫⁻ y in ball z r, (ball x₀ R).indicator g y ∂μ ≤ ENNReal.ofReal (A * r ^ β)) :
    ∀ z : E, ∀ r, 0 < r →
      ∫⁻ y in ball z r, (ball x₀ R).indicator g y ∂μ ≤ ENNReal.ofReal (2 * A * r ^ β) := by
  intro z r hr
  have key : ∀ s : Set E, ∫⁻ y in s, (ball x₀ R).indicator g y ∂μ = ∫⁻ y in ball x₀ R ∩ s, g y ∂μ :=
    fun s => by rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
  by_cases hR : R < 0
  · rw [key, ball_eq_empty.2 hR.le, empty_inter, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  obtain ⟨z', hz', hsub⟩ := exists_mem_closedBall_ball_inter_subset x₀ z (not_lt.1 hR) r
  have h2 : (2 : ℝ) ^ β ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
  calc ∫⁻ y in ball z r, (ball x₀ R).indicator g y ∂μ = ∫⁻ y in ball x₀ R ∩ ball z r, g y ∂μ := key _
    _ ≤ ∫⁻ y in ball x₀ R ∩ ball z' (2 * r), g y ∂μ :=
        lintegral_mono_set fun y hy => ⟨hy.1, hsub ⟨hy.2, hy.1⟩⟩
    _ = ∫⁻ y in ball z' (2 * r), (ball x₀ R).indicator g y ∂μ := (key _).symm
    _ ≤ ENNReal.ofReal (A * (2 * r) ^ β) := h z' hz' (2 * r) (by linarith)
    _ ≤ ENNReal.ofReal (2 * A * r ^ β) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.mul_rpow (by norm_num) hr.le]
        have hAr : 0 ≤ A * r ^ β := mul_nonneg hA (Real.rpow_nonneg hr.le _)
        calc A * ((2 : ℝ) ^ β * r ^ β) = (2 : ℝ) ^ β * (A * r ^ β) := by ring
          _ ≤ 2 * (A * r ^ β) := mul_le_mul_of_nonneg_right h2 hAr
          _ = 2 * A * r ^ β := by ring

section PlanarGaussian

open ProbabilityTheory
open scoped NNReal

/-- **Gaussian heat bound at every start.** For every `x₀ ∈ ℂ` and `R` there is `N` such that: if
`∫_{B(c, r)} g ≤ A r^β` for all centres `c ∈ B̄(x₀, R)` and all `0 < r ≤ 1`, with `A ≥ 0` and `β > 0`,
then for EVERY `z ∈ ℂ` and `t ≥ 0` the planar Gaussian averages of `1_{B(x₀, R)} g` with mean `z`
over the variances `s ∈ (0, t]` integrate to at most
`(1024 / 7) (2π)⁻¹ · 2 max A (N A) · (β' / 2)⁻¹ t^{β'/2}`, where `β' = min β 1`. -/
theorem exists_lintegral_Ioc_lintegral_map_prod_gaussianReal_indicator_le_forall (x₀ : ℂ)
    (R : ℝ) :
    ∃ N : ℕ, ∀ g : ℂ → ℝ≥0∞, Measurable g → ∀ A β : ℝ, 0 ≤ A → 0 < β →
      (∀ c ∈ closedBall x₀ R, ∀ r, 0 < r → r ≤ 1 →
        ∫⁻ y in ball c r, g y ≤ ENNReal.ofReal (A * r ^ β)) →
      ∀ z : ℂ, ∀ t, 0 ≤ t →
        ∫⁻ s in Ioc 0 t, ∫⁻ y, (ball x₀ R).indicator g y ∂(((gaussianReal z.re s.toNNReal).prod
            (gaussianReal z.im s.toNNReal)).map Complex.measurableEquivRealProd.symm) ≤
          ENNReal.ofReal (1024 / 7 / (2 * Real.pi) * (2 * max A (N * A)) / (min β 1 / 2) *
            t ^ (min β 1 / 2)) := by
  obtain ⟨N, hN⟩ := exists_setLIntegral_ball_indicator_le x₀ R
  refine ⟨N, fun g hg A β hA hβ hsmall z t ht => ?_⟩
  have hmax : 0 ≤ max A (N * A) := le_max_of_le_left hA
  have hall := setLIntegral_ball_indicator_le_of_forall_mem_closedBall volume g x₀ hmax
    (min_le_right β 1) (hN volume g A β hA hβ.le hsmall)
  exact lintegral_Ioc_lintegral_map_prod_gaussianReal_le z (hg.indicator measurableSet_ball)
    (lt_min hβ one_pos) (min_le_right β 1) (mul_nonneg zero_le_two hmax) (hall z) ht

end PlanarGaussian

end LatticeProb
