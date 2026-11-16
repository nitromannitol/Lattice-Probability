import LatticeProb.LQG.CompactBallLimitPower

/-! # Non-atomicity from compact-center ball bounds -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- A finite positive-power ball bound forces all singleton masses on the set to vanish. -/
theorem singleton_eq_zero_of_ball_power_bound {μ : Measure ℂ} {K : Set ℂ} {κ : ℝ}
    (hκ : 0 < κ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ)) :
    ∀ z ∈ K, μ {z} = 0 := by
  intro z hz
  have ht : Tendsto (fun n : ℕ => C * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ κ))
      atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) ^ κ) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).rpow_const_nhds_zero hκ
    have henn : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ κ))
        atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul henn (Or.inr hC.ne)
  have hle : ∀ᶠ n : ℕ in atTop,
      μ {z} ≤ C * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ κ) := by
    filter_upwards with n
    have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    have hr1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (measure_mono (singleton_subset_iff.2 (Metric.mem_ball_self hr))).trans
      (hbound z hz _ hr hr1)
  exact le_antisymm (ge_of_tendsto ht hle) zero_le

/-- The LQG area measure has zero singleton masses simultaneously on a compact set. -/
theorem ae_singleton_eq_zero_on_compact_of_isLQGAreaOf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    ∀ᵐ ω ∂P, ∀ z ∈ K, μ ω {z} = 0 := by
  obtain ⟨κ, hκ, hevent⟩ :=
    ae_exists_compact_center_ball_power_bound_of_isLQGAreaOf hH hHm hγ hγ2 hp hpq hq K hK μ hμ
  filter_upwards [hevent] with ω ⟨C, hC, hbound⟩
  exact singleton_eq_zero_of_ball_power_bound hκ hC hbound

/-- The LQG area measure has zero singleton masses simultaneously throughout the plane. -/
theorem ae_singleton_eq_zero_of_isLQGAreaOf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, μ ω {z} = 0 := by
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ z ∈ Metric.closedBall (0 : ℂ) n,
      μ ω {z} = 0 := by
    intro n
    exact ae_singleton_eq_zero_on_compact_of_isLQGAreaOf hH hHm hγ hγ2 hp hpq hq
      _ (isCompact_closedBall 0 n) μ hμ
  filter_upwards [ae_all_iff.2 hevent] with ω hω z
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  exact hω n z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le)

end LatticeProb.LQG
