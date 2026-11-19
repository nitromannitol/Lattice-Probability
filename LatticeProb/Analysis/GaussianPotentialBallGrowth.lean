import Mathlib

/-!
# Gaussian potentials of measures with power growth on balls

Let `λ` be a measure on a normed group and suppose that `λ(B(z, r)) ≤ A r^β` for every `r > 0`.
Splitting space into the annuli `n √s ≤ |x - z| < (n + 1) √s` gives

`∫ exp(-|x - z|² / (2s)) λ(dx) ≤ K_β A s^{β/2}`,  `K_β = ∑_{n ≥ 0} (n + 1)^β e^{-n/2}`,

and hence, for the planar heat kernel `p_s(z, x) = (2πs)⁻¹ exp(-|x - z|² / (2s))` of standard
planar Brownian motion, `∫ p_s(z, x) λ(dx) ≤ (2π)⁻¹ K_β A s^{β/2 - 1}`.

## Main statements

* `LatticeProb.summable_ballGrowthGaussianSeries`: the series defining `K_β` converges.
* `LatticeProb.lintegral_exp_neg_sq_div_le_of_ball_le`: the Gaussian potential bound.
* `LatticeProb.lintegral_heatKernel_le_of_ball_le`: the heat-kernel potential bound.
-/

open MeasureTheory Metric Set Filter

namespace LatticeProb

/-- The terms `(n + 1)^β e^{-n/2}` of the constant `K_β`. -/
noncomputable def ballGrowthGaussianTerm (β : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ β * Real.exp (-(n : ℝ) / 2)

/-- The constant `K_β = ∑_{n ≥ 0} (n + 1)^β e^{-n/2}` of the Gaussian potential bound. -/
noncomputable def ballGrowthGaussianConst (β : ℝ) : ℝ :=
  ∑' n : ℕ, ballGrowthGaussianTerm β n

theorem ballGrowthGaussianTerm_nonneg (β : ℝ) (n : ℕ) : 0 ≤ ballGrowthGaussianTerm β n :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

/-- The series `∑ (n + 1)^β e^{-n/2}` converges for every real `β`. -/
theorem summable_ballGrowthGaussianSeries (β : ℝ) : Summable (ballGrowthGaussianTerm β) := by
  set m : ℕ := ⌈β⌉₊
  have hg : Summable fun n : ℕ => ((n : ℝ) + 1) ^ m * Real.exp (-(n : ℝ) / 2) := by
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul m (by norm_num : (0 : ℝ) < 1 / 2)
    have h1 := ((summable_nat_add_iff 1).2 h0).mul_left (Real.exp (1 / 2))
    refine h1.congr fun n => ?_
    push_cast
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  refine Summable.of_nonneg_of_le (ballGrowthGaussianTerm_nonneg β) (fun n => ?_) hg
  unfold ballGrowthGaussianTerm
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (Nat.le_ceil β)

theorem ballGrowthGaussianConst_nonneg (β : ℝ) : 0 ≤ ballGrowthGaussianConst β :=
  tsum_nonneg (ballGrowthGaussianTerm_nonneg β)

variable {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Pointwise domination of the Gaussian weight by indicators of the balls `B(z, (n + 1) √s)`. -/
theorem ofReal_exp_neg_sq_div_le_tsum_indicator {s : ℝ} (hs : 0 < s) (z x : E) :
    ENNReal.ofReal (Real.exp (-‖x - z‖ ^ 2 / (2 * s))) ≤
      ∑' n : ℕ, (ball z (((n : ℝ) + 1) * Real.sqrt s)).indicator
        (fun _ => ENNReal.ofReal (Real.exp (-(n : ℝ) / 2))) x := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  set y : ℝ := ‖x - z‖ / Real.sqrt s with hy
  have hy0 : 0 ≤ y := div_nonneg (norm_nonneg _) hsq.le
  set n : ℕ := ⌊y⌋₊
  have hmem : x ∈ ball z (((n : ℝ) + 1) * Real.sqrt s) := by
    rw [mem_ball, dist_eq_norm]
    have := Nat.lt_floor_add_one y
    rwa [hy, div_lt_iff₀ hsq] at this
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast Nat.le_self_pow two_ne_zero n
  have hy2 : y ^ 2 = ‖x - z‖ ^ 2 / s := by
    rw [hy, div_pow, Real.sq_sqrt hs.le]
  have hn2 : (n : ℝ) ≤ ‖x - z‖ ^ 2 / s := by
    rw [← hy2]
    exact hnn.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hny 2)
  have hexp : Real.exp (-‖x - z‖ ^ 2 / (2 * s)) ≤ Real.exp (-(n : ℝ) / 2) := by
    apply Real.exp_le_exp.2
    have : -‖x - z‖ ^ 2 / (2 * s) = -(‖x - z‖ ^ 2 / s) / 2 := by ring
    rw [this]
    linarith
  calc ENNReal.ofReal (Real.exp (-‖x - z‖ ^ 2 / (2 * s)))
        ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) := ENNReal.ofReal_le_ofReal hexp
    _ = (ball z (((n : ℝ) + 1) * Real.sqrt s)).indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(n : ℝ) / 2))) x :=
        (indicator_of_mem hmem (fun _ => ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)))).symm
    _ ≤ ∑' k : ℕ, (ball z (((k : ℝ) + 1) * Real.sqrt s)).indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(k : ℝ) / 2))) x :=
        ENNReal.le_tsum (f := fun k : ℕ => (ball z (((k : ℝ) + 1) * Real.sqrt s)).indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(k : ℝ) / 2))) x) n

/-- **Gaussian potential of a measure with power growth on balls.** If `λ(B(z, r)) ≤ A r^β` for
every `r > 0`, then `∫ exp(-|x - z|² / (2s)) λ(dx) ≤ K_β A s^{β/2}` for every `s > 0`. -/
theorem lintegral_exp_neg_sq_div_le_of_ball_le (μ : Measure E) {z : E} {A β s : ℝ}
    (hA : 0 ≤ A) (hs : 0 < s)
    (hball : ∀ r : ℝ, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (A * r ^ β)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-‖x - z‖ ^ 2 / (2 * s))) ∂μ ≤
      ENNReal.ofReal (A * ballGrowthGaussianConst β * s ^ (β / 2)) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hAs : 0 ≤ A * s ^ (β / 2) := mul_nonneg hA (Real.rpow_nonneg hs.le _)
  have hpow : Real.sqrt s ^ β = s ^ (β / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    congr 1
    ring
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-‖x - z‖ ^ 2 / (2 * s))) ∂μ
        ≤ ∫⁻ x, ∑' n : ℕ, (ball z (((n : ℝ) + 1) * Real.sqrt s)).indicator
            (fun _ => ENNReal.ofReal (Real.exp (-(n : ℝ) / 2))) x ∂μ :=
        lintegral_mono fun x => ofReal_exp_neg_sq_div_le_tsum_indicator hs z x
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) *
          μ (ball z (((n : ℝ) + 1) * Real.sqrt s)) := by
        rw [lintegral_tsum fun n => (measurable_const.indicator measurableSet_ball).aemeasurable]
        congr 1
        funext n
        exact lintegral_indicator_const measurableSet_ball _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) *
          ENNReal.ofReal (A * (((n : ℝ) + 1) * Real.sqrt s) ^ β) :=
        ENNReal.tsum_le_tsum fun n => by
          gcongr
          exact hball _ (by positivity)
    _ = ∑' n : ℕ, ENNReal.ofReal (A * s ^ (β / 2)) *
          ENNReal.ofReal (ballGrowthGaussianTerm β n) := by
        congr 1
        funext n
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hAs,
          ballGrowthGaussianTerm, Real.mul_rpow (by positivity) hsq.le, hpow]
        congr 1
        ring
    _ = ENNReal.ofReal (A * ballGrowthGaussianConst β * s ^ (β / 2)) := by
        rw [ENNReal.tsum_mul_left, ballGrowthGaussianConst,
          ← ENNReal.ofReal_tsum_of_nonneg (ballGrowthGaussianTerm_nonneg β)
            (summable_ballGrowthGaussianSeries β),
          ← ENNReal.ofReal_mul hAs]
        congr 1
        ring

/-- **Heat-kernel potential of a measure with power growth on balls.** If `λ(B(z, r)) ≤ A r^β`
for every `r > 0`, then for the planar heat kernel `p_s(z, x) = (2πs)⁻¹ exp(-|x - z|² / (2s))`,
`∫ p_s(z, x) λ(dx) ≤ (2π)⁻¹ K_β A s^{β/2 - 1}` for every `s > 0`. -/
theorem lintegral_heatKernel_le_of_ball_le (μ : Measure E) {z : E} {A β s : ℝ}
    (hA : 0 ≤ A) (hs : 0 < s)
    (hball : ∀ r : ℝ, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (A * r ^ β)) :
    ∫⁻ x, ENNReal.ofReal ((2 * Real.pi * s)⁻¹ * Real.exp (-‖x - z‖ ^ 2 / (2 * s))) ∂μ ≤
      ENNReal.ofReal (A * ballGrowthGaussianConst β / (2 * Real.pi) * s ^ (β / 2 - 1)) := by
  have hc : 0 ≤ (2 * Real.pi * s)⁻¹ := by positivity
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (2 * Real.pi * s)⁻¹ *
        ∫⁻ x, ENNReal.ofReal (Real.exp (-‖x - z‖ ^ 2 / (2 * s))) ∂μ
      ≤ ENNReal.ofReal (2 * Real.pi * s)⁻¹ *
          ENNReal.ofReal (A * ballGrowthGaussianConst β * s ^ (β / 2)) := by
        gcongr
        exact lintegral_exp_neg_sq_div_le_of_ball_le μ hA hs hball
    _ = ENNReal.ofReal (A * ballGrowthGaussianConst β / (2 * Real.pi) * s ^ (β / 2 - 1)) := by
        rw [← ENNReal.ofReal_mul hc, Real.rpow_sub hs, Real.rpow_one]
        congr 1
        field_simp
