import Mathlib
import LatticeProb.LQG.MarkedRootingLimit
import LatticeProb.LQG.GMCL1Convergence

/-!
# The marked rooting identity in the unit disk

For a whole-plane Gaussian free field `h`, `0 < γ < 2`, a `γ`-Liouville quantum gravity measure `μ` of `h`,
a nonnegative continuous `g` with compact support in the open unit disk and a bounded nonnegative continuous
function `F` of finitely many pairings `(h, φ_i)` with test functions,
`E [F ((h, φ_i)_i) ∫ g dμ] = ∫ g(z) E [F ((h, φ_i) + γ ∫ φ_i(x) Cov (h(x), h(z)) dx)_i] dz`.
It is the limit of the approximate Palm identity `integral_mul_integral_lqgApprox_eq` along the dyadic scales:
the left-hand sides converge by the `L¹` convergence of the approximations, the right-hand sides by dominated
convergence, using the covariance limits of `LatticeProb.LQG.MarkedRootingCov`.

## Main statements

* `LatticeProb.integrable_of_tendsto_ae_of_integral_le`, `LatticeProb.tendsto_integral_mul_of_tendsto_L1`:
  Fatou integrability of a nonnegative a.e. limit; passage to the limit in `E [f a_k]` under `L¹` convergence.
* `LatticeProb.Gauss.IsWholePlaneGFF.integrable_integral_lqgApprox`: the mass of the approximations is integrable.
* `LatticeProb.Gauss.IsWholePlaneGFF.integral_mul_integral_lqgMeasure_eq_of_tsupport_subset_ball`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace LatticeProb

/-- A nonnegative a.e. limit of integrable functions with bounded integrals is integrable (Fatou). -/
theorem integrable_of_tendsto_ae_of_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → Ω → ℝ} {A : Ω → ℝ} {C : ℝ} (ha : ∀ k, Integrable (a k) P) (ha0 : ∀ k ω, 0 ≤ a k ω)
    (hA0 : ∀ ω, 0 ≤ A ω) (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => a k ω) atTop (𝓝 (A ω)))
    (hC : ∀ k, ∫ ω, a k ω ∂P ≤ C) : Integrable A P := by
  have hAm : AEStronglyMeasurable A P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (ha k).aestronglyMeasurable) hlim
  refine ⟨hAm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hA0)).2 ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (A ω) ∂P
      = ∫⁻ ω, liminf (fun k => ENNReal.ofReal (a k ω)) atTop ∂P :=
        lintegral_congr_ae (by
          filter_upwards [hlim] with ω hω
          exact ((ENNReal.tendsto_ofReal hω).liminf_eq).symm)
    _ ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (a k ω) ∂P) atTop :=
        lintegral_liminf_le' fun k => (ha k).aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal C := by
        refine liminf_le_of_frequently_le' (Eventually.of_forall fun k => ?_).frequently
        rw [← ofReal_integral_eq_lintegral_ofReal (ha k) (Eventually.of_forall (ha0 k))]
        exact ENNReal.ofReal_le_ofReal (hC k)
    _ < ∞ := ENNReal.ofReal_lt_top

/-- If `a_k → A` in `L¹`, then `E [f a_k] → E [f A]` for a bounded measurable `f`. -/
theorem tendsto_integral_mul_of_tendsto_L1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → Ω → ℝ} {A f : Ω → ℝ} {M : ℝ} (hf : AEStronglyMeasurable f P) (hfb : ∀ ω, ‖f ω‖ ≤ M)
    (ha : ∀ k, Integrable (a k) P) (hA : Integrable A P)
    (hL1 : Tendsto (fun k => ∫ ω, |a k ω - A ω| ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, f ω * a k ω ∂P) atTop (𝓝 (∫ ω, f ω * A ω ∂P)) := by
  have hb : Tendsto (fun k => M * ∫ ω, |a k ω - A ω| ∂P) atTop (𝓝 0) := by
    simpa using hL1.const_mul M
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hb)
  have hI1 : Integrable (fun ω => f ω * a k ω) P :=
    (ha k).bdd_mul hf (Eventually.of_forall hfb)
  have hI2 : Integrable (fun ω => f ω * A ω) P := hA.bdd_mul hf (Eventually.of_forall hfb)
  rw [Real.dist_eq, ← integral_sub hI1 hI2, ← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((ha k).sub hA).abs.const_mul M) (Eventually.of_forall fun ω => ?_)
  rw [← mul_sub, norm_mul, Real.norm_eq_abs (a k ω - A ω)]
  exact mul_le_mul_of_nonneg_right (hfb ω) (abs_nonneg _)

/-- A function with values in `[0, M]` has integral in `[0, M]` against a probability measure. -/
theorem integral_mem_Icc_of_forall {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {M : ℝ} (h : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    0 ≤ ∫ x, f x ∂μ ∧ ∫ x, f x ∂μ ≤ M := by
  refine ⟨integral_nonneg fun x => (h x).1, ?_⟩
  have h1 := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h x).1]; exact (h x).2)
  calc ∫ x, f x ∂μ ≤ ‖∫ x, f x ∂μ‖ := Real.le_norm_self _
    _ ≤ M * μ.real Set.univ := h1
    _ = M := by simp

end LatticeProb

namespace LatticeProb.Gauss

theorem dyadicScale_pos_aux (k : ℕ) : 0 < LQG.dyadicScale k := pow_pos (by norm_num) k

/-- The dyadic scales `2^{-k}` tend to `0` from the right. -/
theorem tendsto_dyadicScale_nhdsGT : Tendsto LQG.dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
  have h : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall fun k => dyadicScale_pos_aux k⟩

/-- The normalization `log max (|z|, 1)` vanishes in the closed unit disk. -/
theorem wholePlaneNormalization_eq_zero {z : ℂ} (hz : ‖z‖ ≤ 1) : wholePlaneNormalization z = 0 := by
  show Real.log (max ‖z‖ 1) = 0
  rw [max_eq_right hz]
  exact Real.log_one

/-- The weight `exp (γ² (Var h_ε(z) + log ε) / 2)` is at most `exp γ²` in the open unit disk, for `ε ≤ 1`. -/
theorem exp_circle_self_add_log_le (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Real.exp (γ ^ 2 * (wholePlaneGFFCov (.circle ε z) (.circle ε z) + Real.log ε) / 2) ≤
      Real.exp (γ ^ 2) := by
  have h := abs_wholePlaneGFFCov_circle_self_add_log_sub_le hε z
  rw [wholePlaneNormalization_eq_zero hz.le, mul_zero, sub_zero] at h
  have hX : wholePlaneGFFCov (.circle ε z) (.circle ε z) + Real.log ε ≤ 2 := by
    linarith [(abs_le.1 h).2]
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_le_mul_of_nonneg_left hX (sq_nonneg γ)]

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The mass `∫ g dλ_ε` of the approximation is a.e. strongly measurable in the field. -/
theorem aestronglyMeasurable_integral_lqgApprox (hh : IsWholePlaneGFF P hC hcirc) {γ ε : ℝ}
    (hε : 0 < ε) {g : ℂ → ℝ} (hgc : Continuous g) :
    AEStronglyMeasurable (fun ω => ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) ε)) P := by
  have := hh.isProbabilityMeasure
  have hf : AEStronglyMeasurable
      (fun p : Ω × ℂ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc p.1 ε p.2) * g p.2) (P.prod volume) :=
    (((Real.measurable_exp.comp_aemeasurable
      ((hh.aemeasurable_circle_uncurry hε volume).const_mul γ)).const_mul (ε ^ (γ ^ 2 / 2))).mul
      (hgc.measurable.comp measurable_snd).aemeasurable).aestronglyMeasurable
  refine (hf.integral_prod_right').congr ?_
  filter_upwards [hh.ae_continuous_circle_slice hε] with ω hω
  exact (LQG.WeylOffOriginDerived.integral_lqgApprox hε.le hω.measurable g).symm

/-- The expected mass of the approximation `λ_ε` against `g` (the approximate Palm identity with `F = 1`). -/
theorem integral_integral_lqgApprox_eq (hh : IsWholePlaneGFF P hC hcirc) {γ ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫ ω, ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) ε) ∂P =
      ∫ z, g z * Real.exp (γ ^ 2 * (wholePlaneGFFCov (.circle ε z) (.circle ε z) + Real.log ε) / 2) := by
  have := hh.isProbabilityMeasure
  have h := hh.integral_mul_integral_lqgApprox_eq (γ := γ) hε hgc hgs hg0 (m := 0)
    (φ := fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (F := fun _ => (1 : ℝ)) continuous_const
    (M := 1) (fun _ => le_rfl) (fun _ => zero_le_one)
  simpa using h

/-- The mass `∫ g dλ_ε` of the approximation is integrable. -/
theorem integrable_integral_lqgApprox (hh : IsWholePlaneGFF P hC hcirc) {γ ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) :
    Integrable (fun ω => ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) ε)) P := by
  by_cases hz : ∀ z, g z = 0
  · obtain rfl : g = 0 := funext hz
    simp
  · obtain ⟨z0, hz0⟩ := not_forall.1 hz
    by_contra hni
    have h := hh.integral_integral_lqgApprox_eq (γ := γ) hε hgc hgs hg0
    rw [integral_undef hni] at h
    have hc : Continuous fun z => g z * Real.exp (γ ^ 2 *
        (wholePlaneGFFCov (.circle ε z) (.circle ε z) + Real.log ε) / 2) :=
      hgc.mul (Real.continuous_exp.comp
        ((continuous_const.mul ((continuous_wholePlaneGFFCov_circle_self hε).add continuous_const)).div_const 2))
    have hpos := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) (x := z0)
      hgs.mul_right (fun z => mul_nonneg (hg0 z) (Real.exp_pos _).le)
      (mul_ne_zero hz0 (Real.exp_pos _).ne')
    linarith

end IsWholePlaneGFF

end LatticeProb.Gauss

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Left-hand side limit.** Along the dyadic scales, `E [F ((h, φ_i)_i) ∫ g dλ_ε] → E [F ((h, φ_i)_i) ∫ g dμ]`
for `g` supported in the open unit disk. -/
theorem tendsto_integral_mul_integral_lqgApprox (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z)
    (hg1 : tsupport g ⊆ Metric.ball 0 1) {m : ℕ} {φ : Fin m → ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F) {M : ℝ}
    (hFM : ∀ x, F x ≤ M) (hF0 : ∀ x, 0 ≤ F x) :
    Tendsto (fun k : ℕ => ∫ ω, F (fun i => hC ω (φ i)) *
        ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k)) ∂P) atTop
      (𝓝 (∫ ω, F (fun i => hC ω (φ i)) * ∫ z, g z ∂(μ ω) ∂P)) := by
  have hP := hh.isProbabilityMeasure
  have hak : ∀ k, Integrable
      (fun ω => ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k))) P := fun k =>
    hh.integrable_integral_lqgApprox (dyadicScale_pos_aux k) hgc hgs hg0
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) (LQG.dyadicScale k))) atTop
      (𝓝 (∫ z, g z ∂(μ ω))) := by
    filter_upwards [hμ] with ω hω
    exact hω.tendsto_integral g hgc hgs
  have hAint : Integrable (fun ω => ∫ z, g z ∂(μ ω)) P := by
    refine integrable_of_tendsto_ae_of_integral_le (C := Real.exp (γ ^ 2) * ∫ z, g z) hak
      (fun k ω => integral_nonneg hg0) (fun ω => integral_nonneg hg0) hlim fun k => ?_
    rw [hh.integral_integral_lqgApprox_eq (dyadicScale_pos_aux k) hgc hgs hg0, ← integral_const_mul]
    have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
    have hc : Continuous fun z => g z * Real.exp (γ ^ 2 *
        (wholePlaneGFFCov (.circle (LQG.dyadicScale k) z) (.circle (LQG.dyadicScale k) z) +
          Real.log (LQG.dyadicScale k)) / 2) :=
      hgc.mul (Real.continuous_exp.comp ((continuous_const.mul
        ((continuous_wholePlaneGFFCov_circle_self (dyadicScale_pos_aux k)).add continuous_const)).div_const 2))
    refine integral_mono (hc.integrable_of_hasCompactSupport hgs.mul_right) (hg.const_mul _) fun z => ?_
    by_cases hz : g z = 0
    · simp [hz]
    · have hzb : ‖z‖ < 1 := mem_ball_zero_iff.1 (hg1 (subset_tsupport g (Function.mem_support.2 hz)))
      have := exp_circle_self_add_log_le γ (dyadicScale_pos_aux k)
        (pow_le_one₀ (by norm_num) (by norm_num)) hzb
      calc g z * _ ≤ g z * Real.exp (γ ^ 2) := mul_le_mul_of_nonneg_left this (hg0 z)
        _ = Real.exp (γ ^ 2) * g z := mul_comm _ _
  have hFm : Measurable fun ω => F (fun i => hC ω (φ i)) :=
    hFc.measurable.comp (measurable_pi_iff.2 fun i => hh.measurable_pairing _ (hφ i))
  exact tendsto_integral_mul_of_tendsto_L1 (M := M) hFm.aestronglyMeasurable
    (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]; exact hFM _) hak hAint
    (hh.tendsto_integral_abs_integral_lqgApprox_sub hγ0 hγ2 hμ hgc hgs hg1)

/-- **Right-hand side limit.** Along the dyadic scales the right-hand sides of the approximate Palm identity
converge to `∫ g(z) E [F ((h, φ_i) + γ ∫ φ_i(x) Cov (h(x), h(z)) dx)_i] dz`, for `g` supported in the open unit
disk. -/
theorem tendsto_integral_weighted_palm (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z)
    (hg1 : tsupport g ⊆ Metric.ball 0 1) {m : ℕ} {φ : Fin m → ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F) {M : ℝ}
    (hFM : ∀ x, F x ≤ M) (hF0 : ∀ x, 0 ≤ F x) :
    Tendsto (fun k : ℕ => ∫ z, g z * Real.exp (γ ^ 2 * (wholePlaneGFFCov (.circle (LQG.dyadicScale k) z)
        (.circle (LQG.dyadicScale k) z) + Real.log (LQG.dyadicScale k)) / 2) *
        ∫ ω, F (fun i => hC ω (φ i) + γ * wholePlaneGFFCov (.pairing (φ i))
          (.circle (LQG.dyadicScale k) z)) ∂P) atTop
      (𝓝 (∫ z, g z * ∫ ω, F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P)) := by
  have hP := hh.isProbabilityMeasure
  have hmeasP : ∀ i, Measurable fun ω => hC ω (φ i) := fun i => hh.measurable_pairing _ (hφ i)
  have hEk_mem : ∀ (k : ℕ) (z : ℂ), 0 ≤ ∫ ω, F (fun i => hC ω (φ i) + γ * wholePlaneGFFCov
      (.pairing (φ i)) (.circle (LQG.dyadicScale k) z)) ∂P ∧ ∫ ω, F (fun i => hC ω (φ i) + γ *
      wholePlaneGFFCov (.pairing (φ i)) (.circle (LQG.dyadicScale k) z)) ∂P ≤ M := fun k z =>
    integral_mem_Icc_of_forall fun ω => ⟨hF0 _, hFM _⟩
  have hEk_meas : ∀ k : ℕ, Measurable fun z : ℂ => ∫ ω, F (fun i => hC ω (φ i) + γ *
      wholePlaneGFFCov (.pairing (φ i)) (.circle (LQG.dyadicScale k) z)) ∂P := fun k => by
    have hsm : ∀ i, Measurable fun z : ℂ =>
        wholePlaneGFFCov (.pairing (φ i)) (.circle (LQG.dyadicScale k) z) := fun i =>
      measurable_wholePlaneGFFCov_pairing_circle (hφ i) (dyadicScale_pos_aux k)
    have hFcm : Measurable fun q : ℂ × Ω => F (fun i => hC q.2 (φ i) + γ *
        wholePlaneGFFCov (.pairing (φ i)) (.circle (LQG.dyadicScale k) q.1)) :=
      hFc.measurable.comp (measurable_pi_iff.2 fun i =>
        ((hmeasP i).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ))
    exact (hFcm.stronglyMeasurable.integral_prod_right').measurable
  have hEk_lim : ∀ z : ℂ, Tendsto (fun k : ℕ => ∫ ω, F (fun i => hC ω (φ i) + γ *
      wholePlaneGFFCov (.pairing (φ i)) (.circle (LQG.dyadicScale k) z)) ∂P) atTop
      (𝓝 (∫ ω, F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P)) := fun z => by
    have hs : ∀ i, Tendsto (fun k : ℕ => wholePlaneGFFCov (.pairing (φ i))
        (.circle (LQG.dyadicScale k) z)) atTop (𝓝 (∫ x, φ i x * wholePlaneCov x z)) := fun i =>
      (tendsto_wholePlaneGFFCov_pairing_circle (hφ i) z).comp tendsto_dyadicScale_nhdsGT
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_) (integrable_const M)
      (fun k => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · exact (hFc.measurable.comp (measurable_pi_iff.2 fun i => (hmeasP i).add_const _)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
      exact hFM _
    · exact (hFc.tendsto _).comp (tendsto_pi_nhds.2 fun i => tendsto_const_nhds.add ((hs i).const_mul γ))
  have hw_cont : ∀ k : ℕ, Continuous fun z : ℂ => Real.exp (γ ^ 2 * (wholePlaneGFFCov
      (.circle (LQG.dyadicScale k) z) (.circle (LQG.dyadicScale k) z) + Real.log (LQG.dyadicScale k)) / 2) :=
    fun k => Real.continuous_exp.comp ((continuous_const.mul
      ((continuous_wholePlaneGFFCov_circle_self (dyadicScale_pos_aux k)).add continuous_const)).div_const 2)
  have hw_lim : ∀ z : ℂ, ‖z‖ < 1 → Tendsto (fun k : ℕ => Real.exp (γ ^ 2 * (wholePlaneGFFCov
      (.circle (LQG.dyadicScale k) z) (.circle (LQG.dyadicScale k) z) + Real.log (LQG.dyadicScale k)) / 2))
      atTop (𝓝 1) := fun z hz => by
    have h1 := (tendsto_wholePlaneGFFCov_circle_self_add_log z).comp tendsto_dyadicScale_nhdsGT
    rw [wholePlaneNormalization_eq_zero hz.le, mul_zero] at h1
    have h2 := (Real.continuous_exp.tendsto (γ ^ 2 * 0 / 2)).comp ((h1.const_mul (γ ^ 2)).div_const 2)
    rw [show γ ^ 2 * 0 / 2 = 0 by ring, Real.exp_zero] at h2
    exact h2
  refine tendsto_integral_of_dominated_convergence (fun z => g z * Real.exp (γ ^ 2) * M) (fun k => ?_) ?_
    (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · exact ((hgc.mul (hw_cont k)).measurable.mul (hEk_meas k)).aestronglyMeasurable
  · exact ((hgc.integrable_of_hasCompactSupport hgs).mul_const _).mul_const _
  · by_cases hz : g z = 0
    · simp [hz]
    · have hzb : ‖z‖ < 1 := mem_ball_zero_iff.1 (hg1 (subset_tsupport g (Function.mem_support.2 hz)))
      have h1 := exp_circle_self_add_log_le γ (dyadicScale_pos_aux k)
        (pow_le_one₀ (by norm_num) (by norm_num)) hzb
      obtain ⟨h2, h3⟩ := hEk_mem k z
      have hw0 := (Real.exp_pos (γ ^ 2 * (wholePlaneGFFCov (.circle (LQG.dyadicScale k) z)
        (.circle (LQG.dyadicScale k) z) + Real.log (LQG.dyadicScale k)) / 2)).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hg0 z) hw0) h2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (hg0 z)) h3 h2
        (mul_nonneg (hg0 z) (Real.exp_pos _).le)
  · by_cases hz : g z = 0
    · simp [hz]
    · have hzb : ‖z‖ < 1 := mem_ball_zero_iff.1 (hg1 (subset_tsupport g (Function.mem_support.2 hz)))
      simpa using ((tendsto_const_nhds (x := g z)).mul (hw_lim z hzb)).mul (hEk_lim z)

/-- **The marked rooting identity in the unit disk.** For a whole-plane Gaussian free field `h`, `0 < γ < 2`, a
`γ`-LQG measure `μ` of `h`, a nonnegative continuous `g` with compact support in the open unit disk and a bounded
nonnegative continuous `F` of finitely many pairings `(h, φ_i)`,
`E [F ((h, φ_i)_i) ∫ g dμ] = ∫ g(z) E [F ((h, φ_i) + γ ∫ φ_i(x) Cov (h(x), h(z)) dx)_i] dz`. -/
theorem integral_mul_integral_lqgMeasure_eq_of_tsupport_subset_ball (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z)
    (hg1 : tsupport g ⊆ Metric.ball 0 1) {m : ℕ} {φ : Fin m → ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F) {M : ℝ}
    (hFM : ∀ x, F x ≤ M) (hF0 : ∀ x, 0 ≤ F x) :
    ∫ ω, F (fun i => hC ω (φ i)) * ∫ z, g z ∂(μ ω) ∂P =
      ∫ z, g z * ∫ ω, F (fun i => hC ω (φ i) + γ * ∫ x, φ i x * wholePlaneCov x z) ∂P := by
  refine tendsto_nhds_unique (hh.tendsto_integral_mul_integral_lqgApprox hγ0 hγ2 hμ hgc hgs hg0 hg1 hφ hFc hFM hF0)
    ((hh.tendsto_integral_weighted_palm hgc hgs hg0 hg1 hφ hFc hFM hF0 (γ := γ)).congr fun k => ?_)
  exact (hh.integral_mul_integral_lqgApprox_eq (dyadicScale_pos_aux k) hgc hgs hg0 hφ hFc hFM hF0).symm

end IsWholePlaneGFF

end LatticeProb.Gauss
