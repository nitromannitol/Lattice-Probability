import LatticeProb.LQG.LQGMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.PosMoment

/-! # Positive moments of recentred square approximations -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.LQG

open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3

/-- The normalized density is the density of the rescaled, recentred
circle-average approximation on every measurable set. -/
theorem lqgApprox_rescale_recentred_eq_lintegral {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (ω : Ω) (γ : ℝ) (z : ℂ)
    {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) {S : Set ℂ} (hS : MeasurableSet S) :
    lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (r / ε) S =
      ∫⁻ w in S, nDens γ H z ε r w ω := by
  rw [lqgApprox, withDensity_apply _ hS]
  congr 1
  funext w
  simp only [nDens, mul_div_cancel₀ r hε]

/-- Uniform positive moments of the normalized recentred approximations on
centered dyadic squares. The regularization index is arbitrary. -/
theorem exists_lintegral_recentred_square_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ}
    (hγ : 0 < γ) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ε : ℝ) (m k : ℕ), 0 < ε →
      QuantumZipper.radius m ≤ ε / 2 → ε / 8 < QuantumZipper.radius m →
      ∫⁻ ω, (ENNReal.ofReal (ε⁻¹ ^ 2) *
        lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (QuantumZipper.radius (m + k) / ε)
          (sqQ (sqCorner z (QuantumZipper.radius m)) m)) ^ q ∂P ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_lintegral_sq_rpow_le_pos hH hHm hγ hq1 hq
  refine ⟨C, hC, ?_⟩
  intro z ε m k hε hupper hlower
  simpa only [lqgApprox_rescale_recentred_eq_lintegral H _ γ z hε.ne'
    (QuantumZipper.radius (m + k)) (measurableSet_sqQ _ _)] using
    hbound z ε m k hε hupper hlower

end LatticeProb.LQG
