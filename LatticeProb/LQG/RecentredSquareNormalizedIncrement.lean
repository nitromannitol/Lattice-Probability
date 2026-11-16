import LatticeProb.LQG.RecentredSquareFirstMoment

/-! # Increments of normalized recentred square approximations -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- The first moment of the increment of the normalized mass sequence has
geometric decay, uniformly over the center and square scale. -/
theorem lintegral_normalized_recentred_square_increment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) (m n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal |(ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
      lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
        (radius (m + (n + 1)) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal -
      (ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
      lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
        (radius (m + n) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal| ∂P ≤
    ENNReal.ofReal (cRate γ 0 (1 / 4)) *
      ENNReal.ofReal (Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
        ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2))) ^ n := by
  have hc : 0 ≤ (2 * radius m)⁻¹ ^ 2 := sq_nonneg _
  have heq (ω : Ω) :
      ENNReal.ofReal |(ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
        lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + (n + 1)) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal -
        (ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
        lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + n) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal| =
      ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) * ENNReal.ofReal
        |(lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + n) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal -
         (lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + (n + 1)) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal| := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ← mul_sub, abs_mul,
      abs_of_nonneg hc, ENNReal.ofReal_mul hc, abs_sub_comm]
  simp_rw [heq]
  exact lintegral_recentred_square_increment_le_geometric hH hHm hγ hγ2 z m n

end LatticeProb.LQG
