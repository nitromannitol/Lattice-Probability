import LatticeProb.LQG.WeylOffOrigin
import LatticeProb.LQG.LQGMeasureNonatomicOrigin
import LatticeProb.LQG.LQGMeasureExistenceProved

/-! # Local domination for a logarithmic insertion -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG

namespace LatticeProb.LQG

/-- On the unit disc, the LQG measure of a nonnegative logarithmic insertion
 dominates the measure without insertion, provided the latter has no atom at zero. -/
theorem ae_measure_le_insertion_on_unitBall
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ ν : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hzero : ∀ᵐ ω ∂P, ν ω {0} = 0) :
    ∀ᵐ ω ∂P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 → ν ω A ≤ μ ω A := by
  have hw := WeylOffOriginDerived.localLQGInsertionWeylOffOrigin_lp Ω P γ α hC hcirc μ ν
    hG hγ hγ2 hαQ hμ hν
  filter_upwards [hw, hzero] with ω hw hzero A hA hsub
  have hAs : MeasurableSet (A \ {0}) := hA.diff (measurableSet_singleton 0)
  have hnone : (0 : ℂ) ∉ A \ {0} := by simp
  calc
    ν ω A = ν ω (A \ {0}) := (measure_sdiff_null hzero).symm
    _ = ∫⁻ z in A \ {0}, ENNReal.ofReal (‖z‖ ^ (γ * α)) ∂μ ω := hw _ hAs hnone
    _ ≤ ∫⁻ _z in A \ {0}, 1 ∂μ ω := by
      apply setLIntegral_mono' hAs
      intro z hz
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_one (norm_nonneg _) (mem_ball_zero_iff.mp (hsub hz.1)).le
        (mul_nonneg hγ.le hα)
    _ = μ ω (A \ {0}) := by rw [setLIntegral_const, one_mul]
    _ ≤ μ ω A := measure_mono sdiff_subset

/-- The whole-plane LQG measure is dominated on the unit disc by the
measure of a nonnegative logarithmic insertion of the same field. -/
theorem ae_measure_le_insertion_on_unitBall_of_field
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ ν : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) :
    ∀ᵐ ω ∂P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball (0 : ℂ) 1 → ν ω A ≤ μ ω A := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hzero := LQGMeasureNonatomicOrigin.ae_origin_nonatomic_of_stronger_existence
    P γ 0 (lqgQ γ / 2) hγ hγ2 (by linarith) (by linarith) hC hcirc
    (lqgMeasureExistenceLP_proved P γ (lqgQ γ / 2) hC hcirc) ν hG hν
  exact ae_measure_le_insertion_on_unitBall P γ α hγ hγ2 hα hαQ hC hcirc μ ν hG hμ hν hzero

end LatticeProb.LQG
