import LatticeProb.LQG.CompactUniformPowerExponent
import LatticeProb.LQG.CompactBallLimitPower

/-! # Simultaneous compact-center bounds for vague limits -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumZipper
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

namespace LatticeProb.LQG

/-- One positive exponent and one almost-sure event give compact-center ball bounds
for a locally finite vague limit of the same approximants. -/
theorem ae_forall_compact_center_ball_power_bound_of_vague_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitOn univ
      (fun n => lqgApprox γ (fun s w => H s w ω) (radius n)) (μ ω)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨κ, hκ, hb⟩ :=
    ae_forall_compact_center_ball_approximant_power_bound hH hHm hγ hγ2 hp hpq hq
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hb, hμ] with ω hb hμ K hK
  obtain ⟨C, hC, hb⟩ := hb K hK
  refine ⟨C, hC, ?_⟩
  intro z hz r hr hr1
  apply measure_open_le_of_isVagueLimitOn hμ Metric.isOpen_ball Metric.isBounded_ball
  · refine ⟨z + (r + 1 : ℝ), ?_⟩
    simp only [mem_compl_iff, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ r + 1 by linarith), not_lt]
    linarith
  · exact hb z hz r hr hr1

/-- The simultaneous compact-center bound for an LQG area measure of the given field. -/
theorem ae_forall_compact_center_ball_power_bound_of_isLQGAreaOf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ) := by
  apply ae_forall_compact_center_ball_power_bound_of_vague_limit hH hHm hγ hγ2 hp hpq hq μ
  filter_upwards [hμ] with ω ⟨hloc, hconv⟩
  have := hloc
  refine ⟨by simp, fun S hS _ => hS.measure_lt_top, fun f hf hfc _ => ?_⟩
  simpa only [lqgApprox, MatedCRTHarmonic.GMSLemma27.lqgApprox,
    MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius] using hconv f hf hfc

end LatticeProb.LQG
