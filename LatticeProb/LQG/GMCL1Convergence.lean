import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.Prob.SummableIncrementsL1
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# L¹ convergence of circle-average Gaussian multiplicative chaos inside the unit disk

Let `h` be a whole-plane Gaussian free field with circle averages `h_ε(z)`, normalized by `h_1(0) = 0`, let
`0 < γ < 2` and let `μ` be the γ-LQG measure of `h`, the almost sure vague limit of the approximations
`ε_k^{γ²/2} e^{γ h_{ε_k}(z)} dz` along the dyadic scales `ε_k = 2^{-k}` (Duplantier-Sheffield, Proposition 1.1).
For a continuous `g` with compact support in the open unit disk, `∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}} dz) → ∫ g dμ`
in `L¹(P)`.

Inside the unit disk the normalization `h_1(0) = 0` makes the approximations equal almost surely to their
versions recentred at `h_1(0)`, whose increments between consecutive dyadic scales have summable `L¹` norms
(`IsWholePlaneGFF.integral_abs_integral_increment_le_exp`); a sequence with summable `L¹` increments and an almost
sure limit converges to it in `L¹` (`SummableIncrements.tendsto_integral_abs_sub_of_integral_abs_sub_le`).

## Main results

* `exists_norm_add_dyadicScale_le_one`: a compact subset `K` of the open unit disk satisfies
  `‖z‖ + 2^{-(k + k₀)} ≤ 1` on `K` for some `k₀` and all `k`.
* `IsWholePlaneGFF.tendsto_integral_abs_integral_lqgApprox_sub`: the `L¹` convergence
  `E |∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}} dz) - ∫ g dμ| → 0`.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

/-- A compact subset of the open unit disk stays at distance at least `2^{-k₀}` from the unit circle:
`‖z‖ + 2^{-(k + k₀)} ≤ 1` on `K` for all `k`. -/
theorem exists_norm_add_dyadicScale_le_one {K : Set ℂ} (hK : IsCompact K) (hK1 : K ⊆ Metric.ball 0 1) :
    ∃ k₀ : ℕ, ∀ z ∈ K, ∀ k : ℕ, ‖z‖ + LQG.dyadicScale (k + k₀) ≤ 1 := by
  obtain ⟨r, hr1, hr⟩ : ∃ r < (1 : ℝ), ∀ z ∈ K, ‖z‖ ≤ r := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨0, one_pos, by simp [he]⟩
    · obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
      exact ⟨‖z₀‖, mem_ball_zero_iff.mp (hK1 hz₀), fun z hz => isMaxOn_iff.mp hmax z hz⟩
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hr1) (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨k₀, fun z hz k => ?_⟩
  have h1 : (2 : ℝ)⁻¹ ^ (k + k₀) ≤ (2 : ℝ)⁻¹ ^ k₀ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 := hr z hz
  rw [LQG.dyadicScale]
  linarith

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **`L¹` convergence of the dyadic approximations inside the unit disk.** For a whole-plane GFF, `0 < γ < 2`,
a γ-LQG measure `μ` of the field and a continuous `g` with compact support in the open unit disk,
`E |∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}} dz) - ∫ g dμ| → 0` along the dyadic scales `ε_k = 2^{-k}`. -/
theorem tendsto_integral_abs_integral_lqgApprox_sub (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg1 : tsupport g ⊆ Metric.ball 0 1) :
    Tendsto (fun k : ℕ => ∫ ω, |∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k)) -
      ∫ z, g z ∂(μ ω)| ∂P) atTop (𝓝 0) := by
  have := hh.isProbabilityMeasure
  obtain ⟨k₀, hk₀⟩ := exists_norm_add_dyadicScale_le_one hgs.isCompact hg1
  rw [← tendsto_add_atTop_iff_nat k₀]
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hCa : ∀ z, |g z| ≤ C := fun z => by simpa [Real.norm_eq_abs] using hC z
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hgm : Measurable g := hgc.measurable
  -- the shifted scales `ε k = 2^{-(k + k₀)}`
  set ε : ℕ → ℝ := fun k => LQG.dyadicScale (k + k₀) with hεdef
  have hεk : ∀ k, 0 < ε k := fun k => pow_pos (by norm_num) _
  have hdy : ∀ k, ε (k + 1) = ε k / 2 := fun k => by
    simp only [hεdef, LQG.dyadicScale, Nat.add_right_comm k 1 k₀, pow_succ, div_eq_mul_inv]
  have hgR : ∀ k z, g z ≠ 0 → ‖z‖ + ε k ≤ 1 := fun k z hz => hk₀ z (subset_tsupport g hz) k
  -- the thick-point level
  obtain ⟨α, hγα, hα, hb, hc⟩ : ∃ α : ℝ, γ ≤ α ∧ α ≤ 2 * γ ∧ 0 < (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 ∧
      0 < (α - γ) ^ 2 / 2 := by
    rcases lt_or_ge γ 1 with h1 | h1
    · refine ⟨2 * γ, by linarith, le_rfl, by nlinarith, by nlinarith⟩
    · refine ⟨2, by linarith, by linarith, by nlinarith, by nlinarith⟩
  -- the jointly measurable continuous version of the circle averages
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hzint : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ r, 0 < r → ∀ c : ℝ,
      Integrable (fun z => g z * (c * rexp (γ * (hcirc ω r z - hcirc ω 1 0)))) := fun ω hω r hr c =>
    (hgc.mul (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hω r hr).sub continuous_const))))).integrable_of_hasCompactSupport hgs.mul_right
  -- the approximations recentred at `h_1(0)` and their increments
  set Y : ℕ → Ω → ℝ := fun k ω => ∫ z, g z * (ε k ^ (γ ^ 2 / 2) *
    rexp (γ * (hcirc ω (ε k) z - hcirc ω 1 0))) with hYdef
  have heqk : ∀ k, ∀ᵐ ω ∂P, Y (k + 1) ω - Y k ω = ∫ z, g z *
      ((ε k / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε k / 2) z - hcirc ω 1 0)) -
        ε k ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε k) z - hcirc ω 1 0))) := by
    intro k
    filter_upwards [hcont] with ω hω
    simp only [hYdef, hdy k]
    rw [← integral_sub (hzint ω hω _ (by linarith [hεk k]) _) (hzint ω hω _ (hεk k) _)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  set b : ℕ → ℝ := fun k =>
    ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log 1 * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
        (C * π * 4 * ∫ z, |g z|) + 1) / 2 *
        rexp (Real.log (ε k) * ((2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2)) +
      2 * (∫ z, |g z|) * rexp (Real.log 1 * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) *
        rexp (Real.log (ε k) * ((α - γ) ^ 2 / 2)) with hbdef
  have hsum : Summable b :=
    (((summable_nat_add_iff k₀).mpr (Gauss.summable_exp_log_dyadicScale_mul hb)).mul_left _).add
      (((summable_nat_add_iff k₀).mpr (Gauss.summable_exp_log_dyadicScale_mul hc)).mul_left _)
  have hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) P := fun k =>
    (hh.integrable_integral_increment (hεk k) one_pos volume hgm hg (hgR k) γ).congr
      ((heqk k).mono fun ω hω => hω.symm)
  have hbd : ∀ k, ∫ ω, |Y (k + 1) ω - Y k ω| ∂P ≤ b k := fun k => by
    rw [integral_congr_ae ((heqk k).mono fun ω hω => by rw [hω])]
    exact hh.integral_abs_integral_increment_le_exp (hεk k) one_pos hgm hg hCa (hgR k) hγα hα
  have hY : ∀ k, AEStronglyMeasurable (Y k) P := fun k => by
    have h := ((hh.integrable_prod_mul_exp_recentred hHm hHae (hεk k) one_pos volume hgm hg (hgR k)
      γ).const_mul (ε k ^ (γ ^ 2 / 2))).integral_prod_left
    refine h.aestronglyMeasurable.congr ?_
    filter_upwards [hHae] with ω hω
    simp only [hYdef, hω]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  -- by `h_1(0) = 0`, the recentred approximations are the approximations
  have hYeq : ∀ᵐ ω ∂P, ∀ k, Y k ω = ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (ε k)) := by
    filter_upwards [hcont, hh.ae_circleAverage_one_zero] with ω hωc hω0 k
    have hdens : Measurable fun z => ENNReal.ofReal (ε k ^ (γ ^ 2 / 2) * rexp (γ * hcirc ω (ε k) z)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (hωc _ (hεk k)).measurable)))
    rw [LQG.lqgApprox, integral_withDensity_eq_integral_toReal_smul hdens
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [hYdef]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [smul_eq_mul, hω0, sub_zero]
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (hεk k).le _) (Real.exp_pos _).le)]
    ring
  have hL : ∀ᵐ ω ∂P, Tendsto (fun k => Y k ω) atTop (𝓝 (∫ z, g z ∂(μ ω))) := by
    filter_upwards [hμ, hYeq] with ω hlim hω
    simp only [hω]
    exact (hlim.tendsto_integral g hgc hgs).comp (tendsto_add_atTop_nat k₀)
  refine (SummableIncrements.tendsto_integral_abs_sub_of_integral_abs_sub_le hY hint hbd hsum hL).congr
    fun k => integral_congr_ae ?_
  filter_upwards [hYeq] with ω hω
  rw [hω k]

end IsWholePlaneGFF

end LatticeProb.Gauss
