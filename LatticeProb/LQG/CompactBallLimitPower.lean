import LatticeProb.LQG.CompactBallApproximantPower
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail

/-! # Compact-center bounds for vague limits -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- A uniform bound on a bounded open set passes to a vague limit. -/
theorem measure_open_le_of_isVagueLimitOn {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn univ μs μ) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : Uᶜ.Nonempty) {a : ℝ≥0∞}
    (ha : ∀ n, μs n U ≤ a) : μ U ≤ a := by
  rw [LQGMeas.measure_open_eq_iSup μ hU hUc]
  apply iSup_le
  intro j
  let f := LQGMeas.openBump U j
  have hf : Continuous f := LQGMeas.continuous_openBump U j
  have hfc : HasCompactSupport f := LQGMeas.hasCompactSupport_openBump hUb j
  have hf0 : ∀ z, 0 ≤ f z := LQGMeas.openBump_nonneg U j
  have hint : Integrable f μ := QuantumZipper.GoodSample.integrable_of_tsupport
    hμ.2.1 hf hfc (subset_univ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)]
  apply le_of_tendsto' (ENNReal.tendsto_ofReal (hμ.2.2 f hf hfc (subset_univ _)))
  intro n
  calc
    ENNReal.ofReal (∫ z, f z ∂μs n) ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂μs n := by
      by_cases hi : Integrable f (μs n)
      · exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf0))
      · simp [integral_undef hi]
    _ ≤ ∫⁻ z, U.indicator 1 z ∂μs n := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ U
      · simp only [indicator_of_mem hz, Pi.one_apply]
        exact ENNReal.ofReal_le_one.2 (LQGMeas.openBump_le_one U j z)
      · have hz0 : f z = 0 := by
          by_contra h
          exact hz (LQGMeas.tsupport_openBump_subset U j (subset_tsupport _ h))
        simp [hz, hz0]
    _ = μs n U := lintegral_indicator_one hU.measurableSet
    _ ≤ a := ha n

/-- The compact-center bound passes to any locally finite vague limit of the same approximants. -/
theorem ae_exists_compact_center_ball_power_bound_of_vague_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitOn univ
      (fun n => lqgApprox γ (fun s w => H s w ω) (radius n)) (μ ω)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨κ, hκ, hb⟩ :=
    ae_exists_compact_center_ball_approximant_power_bound hH hHm hγ hγ2 hp hpq hq K hK
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hb, hμ] with ω hb hμ
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro z hz r hr hr1
  apply measure_open_le_of_isVagueLimitOn hμ Metric.isOpen_ball Metric.isBounded_ball
  · refine ⟨z + (r + 1 : ℝ), ?_⟩
    simp only [mem_compl_iff, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ r + 1 by linarith), not_lt]
    linarith
  · exact hb z hz r hr hr1

/-- The compact-center bound for an LQG measure of the given circle-average process. -/
theorem ae_exists_compact_center_ball_power_bound_of_isLQGAreaOf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ) := by
  apply ae_exists_compact_center_ball_power_bound_of_vague_limit hH hHm hγ hγ2 hp hpq hq K hK μ
  filter_upwards [hμ] with ω ⟨hloc, hconv⟩
  have := hloc
  refine ⟨by simp, fun S hS _ => hS.measure_lt_top, fun f hf hfc _ => ?_⟩
  simpa only [lqgApprox, MatedCRTHarmonic.GMSLemma27.lqgApprox,
    MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius] using hconv f hf hfc

end LatticeProb.LQG
