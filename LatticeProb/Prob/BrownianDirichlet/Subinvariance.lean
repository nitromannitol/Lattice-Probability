import LatticeProb.Prob.BrownianDirichlet.JointMeasurability
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Prob.BrownianPathHarmonicExit
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Lebesgue subinvariance of killed Brownian evaluation

Nonnegative data evaluated before exit define a measurable killed operator.
Translation invariance of Euclidean volume gives subinvariance without an
integrability assumption. Probability normalization gives the unit bound and
zero-start continuity gives the identity at time zero.
-/

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

/-- Nonnegative evaluation of the shifted scaled path, killed at its first exit. -/
noncomputable def killedNN (B : Set (Euc d)) (σ : ℝ)
    (μ : Measure (BrownianPath d)) (t : ℝ≥0) (b : Euc d → ℝ≥0∞)
    (x : Euc d) : ℝ≥0∞ :=
  ∫⁻ ω, if (t : ℝ≥0∞) < scaledExit B σ x ω then b (x + σ • ω t) else 0 ∂μ

/-- Measurable data give a measurable killed operator in the starting point. -/
theorem measurable_killedNN {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} [SFinite μ] (t : ℝ≥0)
    {b : Euc d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (killedNN B σ μ t b) := by
  exact ((measurable_killed_integrand hB σ hb).comp
    (measurable_const.prodMk measurable_id)).lintegral_prod_right'

/-- Euclidean volume is subinvariant for evaluation killed on leaving an open set. -/
theorem lintegral_killedNN_le {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {b : Euc d → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ x in B, killedNN B σ μ t b x) ≤ ∫⁻ x in B, b x := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hmeas : Measurable (fun p : Euc d × BrownianPath d ↦
      B.indicator b (p.1 + σ • p.2 t)) :=
    (hb.indicator hB.measurableSet).comp
      (continuous_fst.add
        (((continuous_eval_const t).comp continuous_snd).const_smul σ)).measurable
  calc
    _ ≤ ∫⁻ x in B, ∫⁻ ω, B.indicator b (x + σ • ω t) ∂μ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro ω
      by_cases ht : (t : ℝ≥0∞) < scaledExit B σ x ω
      · simp only [if_pos ht, indicator_of_mem (mem_of_lt_scaledExit ht)]
        exact le_rfl
      · simp only [if_neg ht]
        exact bot_le
    _ ≤ ∫⁻ x, ∫⁻ ω, B.indicator b (x + σ • ω t) ∂μ :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ ω, ∫⁻ x, B.indicator b (x + σ • ω t) ∂volume ∂μ :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ ω, (∫⁻ x in B, b x) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [lintegral_add_right_eq_self, lintegral_indicator hB.measurableSet]
    _ = ∫⁻ x in B, b x := by simp only [lintegral_const, measure_univ, mul_one]

/-- Data bounded by one give a killed expectation bounded by one. -/
theorem killedNN_le_one (B : Set (Euc d)) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {b : Euc d → ℝ≥0∞} (hb : ∀ x, b x ≤ 1) (x : Euc d) :
    killedNN B σ μ t b x ≤ 1 := by
  letI : IsProbabilityMeasure μ := hμ.1
  calc
    _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro ω
      dsimp only
      split_ifs
      · exact hb _
      · exact bot_le
    _ = 1 := by simp only [lintegral_const, measure_univ, mul_one]

/-- At an interior starting point the killed operator at time zero is the identity. -/
theorem killedNN_zero_time {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (b : Euc d → ℝ≥0∞) {x : Euc d} (hx : x ∈ B) :
    killedNN B σ μ 0 b x = b x := by
  letI : IsProbabilityMeasure μ := hμ.1
  calc
    _ = ∫⁻ _ω, b x ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
      have hpos := scaledExit_pos hB σ hx hω
      simp only [ENNReal.coe_zero, if_pos hpos, hω, smul_zero, add_zero]
    _ = b x := by simp only [lintegral_const, measure_univ, mul_one]

/-- The time-zero identity applies to an existing Brownian law on the Euclidean unit ball. -/
theorem exists_killedNN_unitBall_zero_time :
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧
      killedNN (Metric.ball (0 : Euc 1) 1) 1 μ 0 (fun _ ↦ 1) 0 = 1 := by
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  refine ⟨μ, hμ, ?_⟩
  exact killedNN_zero_time Metric.isOpen_ball 1 hμ (fun _ ↦ 1)
    (Metric.mem_ball_self zero_lt_one)

end LatticeProb
