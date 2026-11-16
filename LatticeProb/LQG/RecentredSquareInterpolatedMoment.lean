import LatticeProb.LQG.RecentredSquareFirstMoment
import LatticeProb.MeasureTheory.MomentInterpolation

/-! # Interpolated moments of recentred square increments -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- Intermediate moments of normalized consecutive square increments have a
geometric bound, uniformly in the square and using one recentred process. -/
theorem exists_lintegral_recentred_square_increment_interpolated_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q θ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    1 < θ + (1 - θ) * q ∧
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ (z : ℂ) (m n : ℕ),
      ∫⁻ ω, (ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) * ENNReal.ofReal
        |(lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + n) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal -
         (lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + (n + 1)) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal|)
          ^ (θ + (1 - θ) * q) ∂P ≤
        (ENNReal.ofReal (cRate γ 0 (1 / 4)) *
          ENNReal.ofReal (Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
            ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2))) ^ n) ^ θ * B ^ (1 - θ) := by
  constructor
  · nlinarith
  obtain ⟨B, hB, hbound⟩ := exists_lintegral_recentred_square_increment_rpow_le hH hHm hγ hq1 hq
  refine ⟨B, hB, ?_⟩
  intro z m n
  let ε : ℝ := 2 * radius m
  have hε : 0 < ε := by dsimp [ε]; exact mul_pos (by norm_num) (radius_pos m)
  let F : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (ε⁻¹ ^ 2) * ENNReal.ofReal
    |(lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (radius (m + k) / ε) (sqQ (sqCorner z (radius m)) m)).toReal -
     (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (radius (m + (k + 1)) / ε) (sqQ (sqCorner z (radius m)) m)).toReal|
  have hF : ∀ k, AEMeasurable (F k) P := by
    intro k
    have hm (j : ℕ) := (measurable_recentred_square_mass hH hHm γ ε hε.ne' z m j).ennreal_toReal
    exact (((hm k).sub (hm (k + 1))).abs.ennreal_ofReal.const_mul _).aemeasurable
  have hfirst : ∀ k, ∫⁻ ω, F k ω ∂P ≤
      ENNReal.ofReal (cRate γ 0 (1 / 4)) *
        ENNReal.ofReal (Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
          ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2))) ^ k := by
    intro k
    simpa only [F, ε] using lintegral_recentred_square_increment_le_geometric hH hHm hγ hγ2 z m k
  have hqbound : ∀ k, ∫⁻ ω, F k ω ^ q ∂P ≤ B := by
    intro k
    have hr := radius_pos m
    simpa only [F, ε] using hbound z (2 * radius m) m k (by positivity)
      (by linarith) (by linarith)
  exact lintegral_rpow_le_of_geometric_first_moment (by linarith) hθ.le hθ1.le hF hfirst hqbound n

end LatticeProb.LQG
