import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.LQG.GMCCircleLaw

/-!
# A uniform tail bound for the maximal mass of the unit ball

For a whole-plane Gaussian free field with circle averages `h_ε(z)` and `0 < γ < 2`, the supremum over the dyadic
scales `ε_n = 2^{-n}` of the mass `μ_n(B(0,1))` of the approximation `μ_n = ε_n^{γ²/2} e^{γ h_{ε_n}(z)} dz`
has a heavy but uniform tail: `P(sup_n μ_n(B(0,1)) > t) ≤ B(γ) / √t`, with `B(γ)` independent of the field.

The proof recentres at the circle of radius `3` about the origin, `μ_n(B(0,1)) ≤ e^{γ h_3(0)} Y_n`
with `Y_n = ∫ g ε_n^{γ²/2} e^{γ (h_{ε_n} - h_3(0))}` for a cutoff `g ≥ 1_{B(0,1)}`, and bounds
`Y_n ≤ |Y_0| + ∑_k |Y_{k+1} - Y_k|` by a random variable `D` of finite mean (first moment of `Y_0` and the `L¹` rate of
the increments).  Because `e^{γ h_3(0)}` and `D` are not independent, one uses
`{t < e^{γ h_3(0)} D} ⊆ {√t < e^{γ h_3(0)}} ∪ {√t < D}` and Markov's inequality for each of the two events.

## Main results

* `ballCutoff`: a continuous cutoff, `1` on `B(0,1)`, supported in `B̄(0,2)`.
* `lqgApprox_ball_le`: the pathwise bound `μ(B(0,1)) ≤ e^{γ h_R(0)} ∫ g ε^{γ²/2} e^{γ (h_ε - h_R(0))}`.
* `IsWholePlaneGFF.measure_maximal_ball_mass_gt_le`: the tail bound with the explicit constant `maximalMassConst γ`.
* `exists_maximal_ball_mass_tail`: the bound with a constant uniform over all whole-plane Gaussian free fields.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology
open scoped ENNReal NNReal

universe u

namespace LatticeProb.Gauss

/-- A continuous cutoff function: `1` on the unit ball `B(0,1)`, `0` outside the ball `B(0,2)`, values in `[0,1]`. -/
noncomputable def ballCutoff (z : ℂ) : ℝ := max 0 (min 1 (2 - ‖z‖))

theorem ballCutoff_continuous : Continuous ballCutoff := by
  unfold ballCutoff
  fun_prop

theorem ballCutoff_nonneg (z : ℂ) : 0 ≤ ballCutoff z := le_max_left _ _

theorem ballCutoff_le_one (z : ℂ) : ballCutoff z ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem ballCutoff_eq_one {z : ℂ} (hz : ‖z‖ < 1) : ballCutoff z = 1 := by
  unfold ballCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem ballCutoff_eq_zero {z : ℂ} (hz : 2 ≤ ‖z‖) : ballCutoff z = 0 := by
  unfold ballCutoff
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem ballCutoff_hasCompactSupport : HasCompactSupport ballCutoff :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun z hz =>
    ballCutoff_eq_zero (by
      have : ¬ ‖z‖ ≤ 2 := fun h => hz (mem_closedBall_zero_iff.mpr h)
      linarith)

/-- **Pathwise bound of the mass of the unit ball.** If `h_ε` is continuous, the mass of `B(0,1)` for the
approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` is at most `e^{γ h_R(0)} ∫ g ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))} dz`. -/
theorem lqgApprox_ball_le {γ : ℝ} {h : ℝ → ℂ → ℝ} {ε : ℝ} (R : ℝ) (hε : 0 < ε) (hcont : Continuous (h ε)) :
    LQG.lqgApprox γ h ε (Metric.ball 0 1) ≤ ENNReal.ofReal (rexp (γ * h R 0) *
      ∫ z, ballCutoff z * (ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - h R 0)))) := by
  have hint : Integrable (fun z => ballCutoff z * (ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - h R 0)))) :=
    (ballCutoff_continuous.mul (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (hcont.sub continuous_const))))).integrable_of_hasCompactSupport
      ballCutoff_hasCompactSupport.mul_right
  have hnn : 0 ≤ᵐ[volume] fun z => ballCutoff z * (ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - h R 0))) :=
    ae_of_all _ fun z => mul_nonneg (ballCutoff_nonneg z) (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
  rw [LQG.lqgApprox, withDensity_apply _ Metric.isOpen_ball.measurableSet, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (hnn.mono fun z hz => mul_nonneg (Real.exp_pos _).le hz),
    ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ Metric.ball (0 : ℂ) 1
  · rw [Set.indicator_of_mem hz, ballCutoff_eq_one (mem_ball_zero_iff.mp hz)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [mul_sub, Real.exp_sub]
    field_simp
  · rw [Set.indicator_of_notMem hz]
    exact zero_le


/-- The thick-point level `α` of the `L¹` rate of the increments: `2γ` for `γ < 1` and `2` for `1 ≤ γ < 2`. -/
noncomputable def thickLevel (γ : ℝ) : ℝ := if γ < 1 then 2 * γ else 2

theorem thickLevel_spec {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    γ ≤ thickLevel γ ∧ thickLevel γ ≤ 2 * γ ∧
      0 < (2 - γ ^ 2 + (2 * γ - thickLevel γ) ^ 2 / 2) / 2 ∧ 0 < (thickLevel γ - γ) ^ 2 / 2 := by
  unfold thickLevel
  split_ifs with h1
  · exact ⟨by linarith, le_rfl, by nlinarith, by nlinarith⟩
  · have h1' := not_lt.mp h1
    exact ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩

/-- The `L¹` bound of the `k`-th increment (radius `R = 3`, cutoff `ballCutoff` bounded by `1`). -/
noncomputable def incrementBound (γ : ℝ) (k : ℕ) : ℝ :=
  ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log 3 * (2 * γ ^ 2 - (2 * γ - thickLevel γ) ^ 2 / 2)) *
        (1 * π * 4 * ∫ z, |ballCutoff z|) + 1) / 2 *
        rexp (Real.log (LQG.dyadicScale k) * ((2 - γ ^ 2 + (2 * γ - thickLevel γ) ^ 2 / 2) / 2)) +
      2 * (∫ z, |ballCutoff z|) * rexp (Real.log 3 * (γ ^ 2 / 2 - (thickLevel γ - γ) ^ 2 / 2)) *
        rexp (Real.log (LQG.dyadicScale k) * ((thickLevel γ - γ) ^ 2 / 2))

theorem incrementBound_nonneg (γ : ℝ) (k : ℕ) : 0 ≤ incrementBound γ k := by
  have hB0 : 0 ≤ rexp (γ ^ 2 * Real.log 2) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hA : 0 ≤ ∫ z, |ballCutoff z| := integral_nonneg fun _ => abs_nonneg _
  unfold incrementBound
  generalize rexp (γ ^ 2 * Real.log 2) - 1 = B0 at hB0 ⊢
  generalize ∫ z, |ballCutoff z| = A at hA ⊢
  positivity

theorem summable_incrementBound {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : Summable (incrementBound γ) := by
  obtain ⟨-, -, hb, hc⟩ := thickLevel_spec hγ0 hγ2
  exact ((summable_exp_log_dyadicScale_mul hb).mul_left _).add
    ((summable_exp_log_dyadicScale_mul hc).mul_left _)

/-- The constant of the tail bound `P(sup_n μ_n(B(0,1)) > t) ≤ maximalMassConst γ / √t`. -/
noncomputable def maximalMassConst (γ : ℝ) : ℝ :=
  rexp (γ ^ 2 * Real.log 3 / 2) + ((∫ z, |ballCutoff z|) * rexp (γ ^ 2 * Real.log 3 / 2) +
    ∑' k, incrementBound γ k)

theorem maximalMassConst_nonneg {γ : ℝ} : 0 ≤ maximalMassConst γ := by
  have hA : 0 ≤ ∫ z, |ballCutoff z| := integral_nonneg fun _ => abs_nonneg _
  unfold maximalMassConst
  have : 0 ≤ ∑' k, incrementBound γ k := tsum_nonneg (incrementBound_nonneg γ)
  positivity

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The random variable `ω ↦ ∫ g(z) e^{γ (h_r(z) - h_R(0))} dν(z)` is integrable. -/
theorem integrable_integral_recentred (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgs : ∀ z, g z ≠ 0 → ‖z‖ + r ≤ R) (γ : ℝ) :
    Integrable (fun ω => ∫ z, g z * rexp (γ * (hcirc ω r z - hcirc ω R 0)) ∂ν) P := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine (hh.integrable_prod_mul_exp_recentred hHm hHae hr hR ν hgm hg hgs γ).integral_prod_left.congr ?_
  filter_upwards [hHae] with ω hω
  simp only [hω]


/-- **Tail of the maximal mass of the unit ball.** For a whole-plane Gaussian free field, `0 < γ < 2` and `t > 0`,
`P(sup_n μ_n(B(0,1)) > t) ≤ maximalMassConst γ / √t`, `μ_n = ε_n^{γ²/2} e^{γ h_{ε_n}(z)} dz`, `ε_n = 2^{-n}`.
The constant depends only on `γ`. -/
theorem measure_maximal_ball_mass_gt_le (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {t : ℝ} (ht : 0 < t) :
    P {ω | ENNReal.ofReal t <
        ⨆ n, LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale n) (Metric.ball 0 1)} ≤
      ENNReal.ofReal (maximalMassConst γ / Real.sqrt t) := by
  have := hh.isProbabilityMeasure
  have hεk : ∀ k, 0 < LQG.dyadicScale k := fun k => pow_pos (by norm_num) k
  have hεk1 : ∀ k, LQG.dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hdy : ∀ k, LQG.dyadicScale (k + 1) = LQG.dyadicScale k / 2 := fun k => by
    rw [LQG.dyadicScale, LQG.dyadicScale, pow_succ, div_eq_mul_inv]
  have hgR : ∀ k z, ballCutoff z ≠ 0 → ‖z‖ + LQG.dyadicScale k ≤ 3 := fun k z hz => by
    have h2 : ‖z‖ < 2 := by
      by_contra h
      exact hz (ballCutoff_eq_zero (not_lt.mp h))
    linarith [hεk1 k]
  have hgm : Measurable ballCutoff := ballCutoff_continuous.measurable
  have hg : Integrable ballCutoff := ballCutoff_continuous.integrable_of_hasCompactSupport
    ballCutoff_hasCompactSupport
  have hCa : ∀ z, |ballCutoff z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (ballCutoff_nonneg z)]
    exact ballCutoff_le_one z
  obtain ⟨hγα, hα, hb, hc⟩ := thickLevel_spec hγ0 hγ2
  have h3 : (0 : ℝ) < 3 := by norm_num
  obtain ⟨H, hHc, -, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hzint : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ r, 0 < r → ∀ c : ℝ,
      Integrable (fun z => ballCutoff z * (c * rexp (γ * (hcirc ω r z - hcirc ω 3 0)))) := fun ω hω r hr c =>
    (ballCutoff_continuous.mul (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hω r hr).sub continuous_const))))).integrable_of_hasCompactSupport
      ballCutoff_hasCompactSupport.mul_right
  set Y : ℕ → Ω → ℝ := fun k ω => ∫ z, ballCutoff z * (LQG.dyadicScale k ^ (γ ^ 2 / 2) *
    rexp (γ * (hcirc ω (LQG.dyadicScale k) z - hcirc ω 3 0))) with hYdef
  have heqk : ∀ k, ∀ᵐ ω ∂P, Y (k + 1) ω - Y k ω = ∫ z, ballCutoff z *
      ((LQG.dyadicScale k / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (LQG.dyadicScale k / 2) z - hcirc ω 3 0)) -
        LQG.dyadicScale k ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (LQG.dyadicScale k) z - hcirc ω 3 0))) := by
    intro k
    filter_upwards [hcont] with ω hω
    simp only [hYdef, hdy k]
    rw [← integral_sub (hzint ω hω _ (by linarith [hεk k]) _) (hzint ω hω _ (hεk k) _)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  have hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) P := fun k =>
    (hh.integrable_integral_increment (hεk k) h3 volume hgm hg (hgR k) γ).congr
      ((heqk k).mono fun ω hω => hω.symm)
  have hbd : ∀ k, ∫ ω, |Y (k + 1) ω - Y k ω| ∂P ≤ incrementBound γ k := fun k => by
    rw [integral_congr_ae ((heqk k).mono fun ω hω => by rw [hω])]
    exact hh.integral_abs_integral_increment_le_exp (hεk k) h3 hgm hg hCa (hgR k) hγα hα
  have hY0 : ∀ ω, Y 0 ω = ∫ z, ballCutoff z * rexp (γ * (hcirc ω 1 z - hcirc ω 3 0)) := fun ω => by
    simp [hYdef, LQG.dyadicScale]
  have hY0i : Integrable (Y 0) P := by
    have := hh.integrable_integral_recentred zero_lt_one h3 volume hgm hg
      (fun z hz => by
        have h := hgR 0 z hz
        rwa [show LQG.dyadicScale 0 = 1 from pow_zero _] at h) γ
    exact this.congr (ae_of_all _ fun ω => (hY0 ω).symm)
  set D : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal |Y 0 ω| +
    ∑' k, ENNReal.ofReal |Y (k + 1) ω - Y k ω| with hD
  have hD0 : AEMeasurable (fun ω => ENNReal.ofReal |Y 0 ω|) P := hY0i.abs.aemeasurable.ennreal_ofReal
  have hDk : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal |Y (k + 1) ω - Y k ω|) P := fun k =>
    (hint k).abs.aemeasurable.ennreal_ofReal
  have hDm : AEMeasurable D P := hD0.add (AEMeasurable.tsum hDk)
  have hsum := summable_incrementBound hγ0 hγ2
  have hA0 : 0 ≤ ∫ z, |ballCutoff z| := integral_nonneg fun _ => abs_nonneg _
  have hS0 : 0 ≤ ∑' k, incrementBound γ k := tsum_nonneg (incrementBound_nonneg γ)
  have hDint : ∫⁻ ω, D ω ∂P ≤ ENNReal.ofReal ((∫ z, |ballCutoff z|) * rexp (γ ^ 2 * Real.log 3 / 2) +
      ∑' k, incrementBound γ k) := by
    have h1 : ∫⁻ ω, ENNReal.ofReal |Y 0 ω| ∂P ≤
        ENNReal.ofReal ((∫ z, |ballCutoff z|) * rexp (γ ^ 2 * Real.log 3 / 2)) := by
      calc ∫⁻ ω, ENNReal.ofReal |Y 0 ω| ∂P
          ≤ ∫⁻ ω, ∫⁻ z, ‖ballCutoff z * rexp (γ * (hcirc ω 1 z - hcirc ω 3 0))‖ₑ ∂volume ∂P := by
            refine lintegral_mono fun ω => ?_
            rw [← Real.enorm_eq_ofReal_abs, hY0]
            exact enorm_integral_le_lintegral_enorm _
        _ = (∫⁻ z, ‖ballCutoff z‖ₑ) * ENNReal.ofReal (rexp (γ ^ 2 * Real.log (3 / 1) / 2)) :=
            hh.lintegral_lintegral_enorm_mul_exp_eq one_pos h3 volume hgm (fun z hz => by
              have h := hgR 0 z hz
              rwa [show LQG.dyadicScale 0 = 1 from pow_zero _] at h) γ
        _ = _ := by
            rw [← ofReal_integral_norm_eq_lintegral_enorm hg, div_one,
              ← ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _)]
            simp only [Real.norm_eq_abs]
    have h2 : ∫⁻ ω, ∑' k, ENNReal.ofReal |Y (k + 1) ω - Y k ω| ∂P ≤
        ENNReal.ofReal (∑' k, incrementBound γ k) := by
      rw [lintegral_tsum hDk, ENNReal.ofReal_tsum_of_nonneg (incrementBound_nonneg γ) hsum]
      refine ENNReal.tsum_le_tsum fun k => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hint k).abs (ae_of_all _ fun _ => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hbd k)
    calc ∫⁻ ω, D ω ∂P = ∫⁻ ω, ENNReal.ofReal |Y 0 ω| ∂P +
          ∫⁻ ω, ∑' k, ENNReal.ofReal |Y (k + 1) ω - Y k ω| ∂P := lintegral_add_left' hD0 _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := (ENNReal.ofReal_add (mul_nonneg hA0 (Real.exp_pos _).le) hS0).symm
  have hpath : ∀ᵐ ω ∂P, (⨆ n, LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale n) (Metric.ball 0 1)) ≤
      ENNReal.ofReal (rexp (γ * hcirc ω 3 0)) * D ω := by
    filter_upwards [hcont] with ω hω
    refine iSup_le fun n => ?_
    refine (lqgApprox_ball_le 3 (hεk n) (hω _ (hεk n))).trans ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine mul_le_mul' le_rfl ?_
    have hn : Y n ω ≤ |Y 0 ω| + ∑ k ∈ Finset.range n, |Y (k + 1) ω - Y k ω| := by
      have := Finset.sum_range_sub (fun k => Y k ω) n
      calc Y n ω = Y 0 ω + ∑ k ∈ Finset.range n, (Y (k + 1) ω - Y k ω) := by rw [this]; ring
        _ ≤ _ := add_le_add (le_abs_self _) (Finset.sum_le_sum fun k _ => le_abs_self _)
    calc ENNReal.ofReal (Y n ω)
        ≤ ENNReal.ofReal (|Y 0 ω| + ∑ k ∈ Finset.range n, |Y (k + 1) ω - Y k ω|) :=
          ENNReal.ofReal_le_ofReal hn
      _ = ENNReal.ofReal |Y 0 ω| + ∑ k ∈ Finset.range n, ENNReal.ofReal |Y (k + 1) ω - Y k ω| := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg _),
            ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg _)]
      _ ≤ D ω := add_le_add_right (ENNReal.sum_le_tsum _) _
  have hH3 := hh.hasLaw_circle_origin (R := 3) h3
  have hv : (((2 * Real.log (max (3 : ℝ) 1) - Real.log 3).toNNReal : ℝ≥0) : ℝ) = Real.log 3 := by
    rw [max_eq_left (by norm_num), Real.coe_toNNReal _
      (by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); linarith)]
    ring
  have hAint : ∫⁻ ω, ENNReal.ofReal (rexp (γ * hcirc ω 3 0)) ∂P =
      ENNReal.ofReal (rexp (γ ^ 2 * Real.log 3 / 2)) := by
    rw [GaussTail.lintegral_ofReal_exp_mul_of_hasLaw hH3 γ, hv]
  have hAm : AEMeasurable (fun ω => ENNReal.ofReal (rexp (γ * hcirc ω 3 0))) P :=
    (Real.measurable_exp.comp_aemeasurable (hH3.aemeasurable.const_mul γ)).ennreal_ofReal
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsne : ENNReal.ofReal (Real.sqrt t) ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hsub : {ω | ENNReal.ofReal t < ⨆ n, LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale n) (Metric.ball 0 1)}
      ≤ᵐ[P] {ω | ENNReal.ofReal (Real.sqrt t) < ENNReal.ofReal (rexp (γ * hcirc ω 3 0))} ∪
        {ω | ENNReal.ofReal (Real.sqrt t) < D ω} := by
    filter_upwards [hpath] with ω hω hmem
    by_contra hnot
    have h1 : ENNReal.ofReal (rexp (γ * hcirc ω 3 0)) ≤ ENNReal.ofReal (Real.sqrt t) :=
      not_lt.mp fun h => hnot (Or.inl h)
    have h2 : D ω ≤ ENNReal.ofReal (Real.sqrt t) := not_lt.mp fun h => hnot (Or.inr h)
    have h4 := mul_le_mul' h1 h2
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt ht.le] at h4
    have hmem' : ENNReal.ofReal t < ⨆ n, LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale n) (Metric.ball 0 1) :=
      hmem
    exact lt_irrefl _ (lt_of_lt_of_le hmem' (hω.trans h4))
  have hM1 : P {ω | ENNReal.ofReal (Real.sqrt t) < ENNReal.ofReal (rexp (γ * hcirc ω 3 0))} ≤
      ENNReal.ofReal (rexp (γ ^ 2 * Real.log 3 / 2) / Real.sqrt t) := by
    calc P {ω | ENNReal.ofReal (Real.sqrt t) < ENNReal.ofReal (rexp (γ * hcirc ω 3 0))}
        ≤ P {ω | ENNReal.ofReal (Real.sqrt t) ≤ ENNReal.ofReal (rexp (γ * hcirc ω 3 0))} :=
          measure_mono (Set.ofPred_subset_ofPred.mpr fun ω hω => hω.le)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (rexp (γ * hcirc ω 3 0)) ∂P) / ENNReal.ofReal (Real.sqrt t) :=
          meas_ge_le_lintegral_div hAm hsne ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (rexp (γ ^ 2 * Real.log 3 / 2) / Real.sqrt t) := by
          rw [hAint, ENNReal.ofReal_div_of_pos hs]
  have hM2 : P {ω | ENNReal.ofReal (Real.sqrt t) < D ω} ≤
      ENNReal.ofReal (((∫ z, |ballCutoff z|) * rexp (γ ^ 2 * Real.log 3 / 2) +
        ∑' k, incrementBound γ k) / Real.sqrt t) := by
    calc P {ω | ENNReal.ofReal (Real.sqrt t) < D ω}
        ≤ P {ω | ENNReal.ofReal (Real.sqrt t) ≤ D ω} := measure_mono (Set.ofPred_subset_ofPred.mpr fun ω hω => hω.le)
      _ ≤ (∫⁻ ω, D ω ∂P) / ENNReal.ofReal (Real.sqrt t) :=
          meas_ge_le_lintegral_div hDm hsne ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((∫ z, |ballCutoff z|) * rexp (γ ^ 2 * Real.log 3 / 2) +
          ∑' k, incrementBound γ k) / ENNReal.ofReal (Real.sqrt t) := ENNReal.div_le_div_right hDint _
      _ = _ := (ENNReal.ofReal_div_of_pos hs).symm
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ((add_le_add hM1 hM2).trans ?_))
  have hK : 0 ≤ (∫ z, |ballCutoff z|) * rexp (γ ^ 2 * Real.log 3 / 2) + ∑' k, incrementBound γ k :=
    add_nonneg (mul_nonneg hA0 (Real.exp_pos _).le) hS0
  rw [← ENNReal.ofReal_add (div_nonneg (Real.exp_pos _).le hs.le) (div_nonneg hK hs.le)]
  refine le_of_eq (congrArg _ ?_)
  unfold maximalMassConst
  ring

/-- **Uniform tail of the maximal mass of the unit ball.** For `0 < γ < 2` there is a constant `B` such that, for
every whole-plane Gaussian free field and every `t > 0`,
`P(sup_n ε_n^{γ²/2} e^{γ h_{ε_n}} dz (B(0,1)) > t) ≤ B / √t`. -/
theorem _root_.LatticeProb.Gauss.exists_maximal_ball_mass_tail {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ B : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
      {hcirc : Ω → ℝ → ℂ → ℝ}, IsWholePlaneGFF P hC hcirc → ∀ {t : ℝ}, 0 < t →
      P {ω | ENNReal.ofReal t <
          ⨆ n, LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale n) (Metric.ball 0 1)} ≤
        ENNReal.ofReal (B / Real.sqrt t) :=
  ⟨maximalMassConst γ, fun hh _ ht => hh.measure_maximal_ball_mass_gt_le hγ0 hγ2 ht⟩

end IsWholePlaneGFF

end LatticeProb.Gauss
