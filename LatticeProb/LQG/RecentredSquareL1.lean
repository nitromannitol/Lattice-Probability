import LatticeProb.LQG.RecentredLevelHyp
import LatticeProb.LQG.RecentredSquareIncrement
import LatticeProb.LQG.RecentredSquareGeometry

/-! # Increment estimates on recentred squares -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper

namespace LatticeProb.LQG

/-- The L¹ increment estimate for a centred dyadic square and the same
coordinate-measurable circle-average process at both levels. -/
theorem integral_abs_recentred_square_increment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ ε : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hε : 0 < ε)
    (z : ℂ) {m k : ℕ} (hm : radius m ≤ ε / 2) (hmk : m ≤ k) :
    ∫ ω, |(lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (radius k / ε) (sqQ (sqCorner z (radius m)) m)).toReal -
        (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (radius (k + 1) / ε) (sqQ (sqCorner z (radius m)) m)).toReal| ∂P ≤
      QuantumZipper.AreaP3b.cRate γ 0 (1 / 4) * ε ^ 2 *
        Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
          ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log (ε / radius k))) := by
  let := hH.isProbabilityMeasure
  have hk : radius k ≤ ε / 2 := (AreaExist.aradius_anti hmk).trans hm
  have hk1 : radius (k + 1) ≤ ε / 2 :=
    (AreaExist.aradius_anti (Nat.le_succ k)).trans hk
  have hS : ∀ t ∈ sqQ (sqCorner z (radius m)) m, ‖t - z‖ ≤ ε / 2 := by
    intro t ht
    exact (norm_sub_le_of_mem_centred_sqQ z m ht).trans hm
  have hb := centred_sqQ_volume_bounds z hm
  exact integral_abs_recentred_increment_le_rate H hγ hγ2 hε z
    (measurableSet_sqQ _ _) hb.1 (by norm_num) hb.2 k
    (levelHyp_recentred_circle hH hHm hε z hk hS)
    (levelHyp_recentred_circle hH hHm hε z hk1 hS)

end LatticeProb.LQG
