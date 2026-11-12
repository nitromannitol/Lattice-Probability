import LatticeProb.LQG.GMCL1Rate
import LatticeProb.LQG.LQGMeasure
import LatticeProb.Prob.SummableIncrements
import LatticeProb.LQG.LQGLimitExists

/-!
# Almost sure convergence of circle-average Gaussian multiplicative chaos along dyadic scales

For a whole-plane Gaussian free field with circle averages `h_ε(z)` and `0 < γ < 2`, the approximations
`ε^{γ²/2} e^{γ h_ε(z)} dz` integrated against a continuous compactly supported test function converge almost
surely along the dyadic scales `ε_k = 2^{-k}` (Duplantier-Sheffield, Proposition 1.1; Berestycki's thick-point
truncation for `γ ≥ √2`).

## Main results

* `IsWholePlaneGFF.integral_abs_integral_increment_le_exp`: the `L¹` rate of the increment between the scales `ε` and
  `ε / 2` for a bounded weight, written as `K₁ ε^{b/2} + K₂ ε^{(α-γ)²/2}` with `b = 2 - γ² + (2γ - α)²/2`
  (the parameter `t` of the thin-point bound chosen as `ε^{(2 - p)/2}`, `p = 2γ² - (2γ - α)²/2`).
* `summable_exp_log_dyadicScale_mul`: `∑_k ε_k^c < ∞` for `c > 0`.
* `IsWholePlaneGFF.ae_exists_tendsto_integral_lqgApprox`: almost sure convergence of
  `∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}} dz)` for every continuous compactly supported `g` and `0 < γ < 2`; the
  thick-point level is `α = 2γ` for `γ < 1` and `α = 2` for `1 ≤ γ < 2`.
* `IsWholePlaneGFF.exists_isLQGMeasure`: existence of the γ-LQG area measure of the whole-plane GFF for
  `0 < γ < 2`, as the almost sure vague limit of the approximations along the dyadic scales.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

/-- `e^{c log ε_k} = (e^{c log (1/2)})^k` for the dyadic scales `ε_k = 2^{-k}`. -/
theorem exp_log_dyadicScale_mul (k : ℕ) (c : ℝ) :
    rexp (Real.log (LQG.dyadicScale k) * c) = rexp (Real.log 2⁻¹ * c) ^ k := by
  rw [LQG.dyadicScale, Real.log_pow, ← Real.exp_nat_mul]
  congr 1
  ring

/-- `∑_k ε_k^c < ∞` along the dyadic scales, for `c > 0`. -/
theorem summable_exp_log_dyadicScale_mul {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => rexp (Real.log (LQG.dyadicScale k) * c) := by
  simp_rw [exp_log_dyadicScale_mul]
  refine summable_geometric_of_lt_one (Real.exp_pos _).le ?_
  exact (Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos (Real.log_neg (by norm_num) (by norm_num)) hc)).trans_eq
    Real.exp_zero

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **L¹ rate in exponential form.** For `|g| ≤ C`, `γ ≤ α ≤ 2γ`, `p = 2γ² - (2γ - α)²/2`,
`b = 2 - γ² + (2γ - α)²/2` and `A = ∫ |g|`,
`E |∫ g Δ| ≤ ((2^{γ²} - 1) R^p · 4π C A + 1)/2 · ε^{b/2} + 2 A R^{γ²/2 - (α-γ)²/2} ε^{(α - γ)²/2}`,
where `Δ` is the increment between the recentred normalized exponentials at radii `ε / 2` and `ε`. -/
theorem integral_abs_integral_increment_le_exp (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 < R) {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤
      ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log R * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (C * π * 4 * ∫ z, |g z|) + 1) / 2 * rexp (Real.log ε * ((2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2)) +
        2 * (∫ z, |g z|) * rexp (Real.log R * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) *
          rexp (Real.log ε * ((α - γ) ^ 2 / 2)) := by
  have hM := hh.integral_abs_integral_increment_le hε hR volume hgm hg hgR hγα hα
    (t := rexp (Real.log ε * ((2 - (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) / 2))) (Real.exp_pos _)
  have hI := Gauss.integral_indicator_norm_sub_lt_le hg hC (2 * ε)
  have hball : volume.real (Metric.ball (0 : ℂ) (2 * ε)) = π * (4 * rexp (Real.log ε * 2)) := by
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal, NNReal.coe_real_pi, ← Real.rpow_def_of_pos hε,
      Real.rpow_two]
    ring
  rw [hball] at hI
  have hL : Real.log (R / ε) = Real.log R - Real.log ε := Real.log_div hR.ne' hε.ne'
  have hεu : ε ^ (γ ^ 2 / 2) = rexp (Real.log ε * (γ ^ 2 / 2)) := Real.rpow_def_of_pos hε _
  have hB0 : 0 ≤ rexp (γ ^ 2 * Real.log 2) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  refine hM.trans ?_
  rw [hL, hεu]
  set u := Real.log ε with hu
  set v := Real.log R with hv
  set A := ∫ z, |g z| with hA
  set B0 := rexp (γ ^ 2 * Real.log 2) - 1 with hB0def
  set p := 2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2 with hp
  set q := γ ^ 2 / 2 - (α - γ) ^ 2 / 2 with hq
  set s := (2 - p) / 2 with hs
  set bb := (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 with hbb
  calc _ ≤ rexp (u * (γ ^ 2 / 2)) * ((B0 * rexp ((v - u) * p) * (C * (π * (4 * rexp (u * 2))) * A) /
          rexp (u * s) + rexp (u * s)) / 2 + 2 * A * rexp ((v - u) * q)) := by
        gcongr
    _ = _ := by
        have k1 : rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * p) * rexp (u * 2) * rexp (-(u * s)) =
            rexp (v * p) * rexp (u * bb) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hbb, hs, hp]
          ring
        have k2 : rexp (u * (γ ^ 2 / 2)) * rexp (u * s) = rexp (u * bb) := by
          rw [← Real.exp_add]
          congr 1
          rw [hbb, hs, hp]
          ring
        have k3 : rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * q) = rexp (v * q) * rexp (u * ((α - γ) ^ 2 / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hq]
          ring
        rw [div_eq_mul_inv _ (rexp (u * s)), ← Real.exp_neg]
        linear_combination (B0 * C * π * 4 * A / 2) * k1 + (1 / 2) * k2 + (2 * A) * k3

/-- **Almost sure convergence along dyadic scales.** For `0 < γ < 2` and a continuous compactly supported `g`,
almost surely `∫ g d(ε_k^{γ²/2} e^{γ h_{ε_k}(z)} dz)` converges as `k → ∞`, `ε_k = 2^{-k}`. -/
theorem ae_exists_tendsto_integral_lqgApprox (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ∀ᵐ ω ∂P, ∃ ℓ : ℝ,
      Tendsto (fun k : ℕ => ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k))) atTop (𝓝 ℓ) := by
  have := hh.isProbabilityMeasure
  -- the support, the bound and the radius `R`
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hgs.isCompact.isBounded
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hCa : ∀ z, |g z| ≤ C := fun z => by simpa [Real.norm_eq_abs] using hC z
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hgm : Measurable g := hgc.measurable
  set R : ℝ := max R0 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hεk : ∀ k, 0 < LQG.dyadicScale k := fun k => pow_pos (by norm_num) k
  have hεk1 : ∀ k, LQG.dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hdy : ∀ k, LQG.dyadicScale (k + 1) = LQG.dyadicScale k / 2 := fun k => by
    rw [LQG.dyadicScale, LQG.dyadicScale, pow_succ, div_eq_mul_inv]
  have hgR : ∀ k z, g z ≠ 0 → ‖z‖ + LQG.dyadicScale k ≤ R := fun k z hz => by
    have h1 : ‖z‖ ≤ R0 := mem_closedBall_zero_iff.mp (hR0 (subset_tsupport g hz))
    have h2 := hεk1 k
    have h3 := le_max_left R0 0
    linarith
  -- the thick-point level
  obtain ⟨α, hγα, hα, hb, hc⟩ : ∃ α : ℝ, γ ≤ α ∧ α ≤ 2 * γ ∧ 0 < (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 ∧
      0 < (α - γ) ^ 2 / 2 := by
    rcases lt_or_ge γ 1 with h1 | h1
    · refine ⟨2 * γ, by linarith, le_rfl, by nlinarith, by nlinarith⟩
    · refine ⟨2, by linarith, by linarith, by nlinarith, by nlinarith⟩
  -- continuity of the circle averages
  obtain ⟨H, hHc, -, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hzint : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ r, 0 < r → ∀ c : ℝ,
      Integrable (fun z => g z * (c * rexp (γ * (hcirc ω r z - hcirc ω R 0)))) := fun ω hω r hr c =>
    (hgc.mul (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hω r hr).sub continuous_const))))).integrable_of_hasCompactSupport hgs.mul_right
  -- the recentred approximations and their increments
  set Y : ℕ → Ω → ℝ := fun k ω => ∫ z, g z * (LQG.dyadicScale k ^ (γ ^ 2 / 2) *
    rexp (γ * (hcirc ω (LQG.dyadicScale k) z - hcirc ω R 0))) with hYdef
  have heqk : ∀ k, ∀ᵐ ω ∂P, Y (k + 1) ω - Y k ω = ∫ z, g z *
      ((LQG.dyadicScale k / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (LQG.dyadicScale k / 2) z - hcirc ω R 0)) -
        LQG.dyadicScale k ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (LQG.dyadicScale k) z - hcirc ω R 0))) := by
    intro k
    filter_upwards [hcont] with ω hω
    simp only [hYdef, hdy k]
    rw [← integral_sub (hzint ω hω _ (by linarith [hεk k]) _) (hzint ω hω _ (hεk k) _)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  set b : ℕ → ℝ := fun k =>
    ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log R * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
        (C * π * 4 * ∫ z, |g z|) + 1) / 2 *
        rexp (Real.log (LQG.dyadicScale k) * ((2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2)) +
      2 * (∫ z, |g z|) * rexp (Real.log R * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) *
        rexp (Real.log (LQG.dyadicScale k) * ((α - γ) ^ 2 / 2)) with hbdef
  have hsum : Summable b :=
    ((Gauss.summable_exp_log_dyadicScale_mul hb).mul_left _).add
      ((Gauss.summable_exp_log_dyadicScale_mul hc).mul_left _)
  have hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) P := fun k =>
    (hh.integrable_integral_increment (hεk k) hR volume hgm hg (hgR k) γ).congr
      ((heqk k).mono fun ω hω => hω.symm)
  have hbd : ∀ k, ∫ ω, |Y (k + 1) ω - Y k ω| ∂P ≤ b k := fun k => by
    rw [integral_congr_ae ((heqk k).mono fun ω hω => by rw [hω])]
    exact hh.integral_abs_integral_increment_le_exp (hεk k) hR hgm hg hCa (hgR k) hγα hα
  have hV := SummableIncrements.ae_exists_tendsto_of_integral_abs_sub_le hint hbd hsum
  -- back to the uncentred approximations
  filter_upwards [hV, hcont] with ω hω hωc
  obtain ⟨ℓ, hℓ⟩ := hω
  refine ⟨rexp (γ * hcirc ω R 0) * ℓ, (hℓ.const_mul _).congr fun k => ?_⟩
  have hdens : Measurable fun z => ENNReal.ofReal (LQG.dyadicScale k ^ (γ ^ 2 / 2) *
      rexp (γ * hcirc ω (LQG.dyadicScale k) z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (hωc _ (hεk k)).measurable)))
  rw [LQG.lqgApprox, integral_withDensity_eq_integral_toReal_smul hdens
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), hYdef, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (hεk k).le _) (Real.exp_pos _).le), mul_sub,
    Real.exp_sub]
  field_simp

/-- **Existence of the γ-LQG measure** of a whole-plane GFF for `0 < γ < 2`: almost surely the approximations
`ε_k^{γ²/2} e^{γ h_{ε_k}(z)} dz`, `ε_k = 2^{-k}`, converge vaguely to a locally finite measure. -/
theorem exists_isLQGMeasure (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ μ : Ω → Measure ℂ, LQG.IsLQGMeasure P γ hcirc μ := by
  classical
  obtain ⟨D, hDc, hDcc, hD⟩ := LQG.exists_countable_determining_isLQGLimit
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ g : D, ∃ ℓ : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, (g : ℂ → ℝ) z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k))) atTop (𝓝 ℓ) :=
    ae_all_iff.mpr fun g => hh.ae_exists_tendsto_integral_lqgApprox hγ0 hγ2 (hDcc g g.2).1 (hDcc g g.2).2
  obtain ⟨H, hHc, -, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hex : ∀ᵐ ω ∂P, ∃ m : Measure ℂ, LQG.IsLQGLimit γ (hcirc ω) m := by
    filter_upwards [hall, hHae] with ω hω hωH
    refine hD γ (hcirc ω) (fun k => ?_) (fun g hg => hω ⟨g, hg⟩)
    rw [← funext (hωH (LQG.dyadicScale k))]
    exact hHc ω _ (pow_pos (by norm_num) k)
  refine ⟨fun ω => if h : ∃ m : Measure ℂ, LQG.IsLQGLimit γ (hcirc ω) m then h.choose else 0, ?_⟩
  filter_upwards [hex] with ω hω
  split_ifs
  exact hω.choose_spec

end IsWholePlaneGFF

end LatticeProb.Gauss
