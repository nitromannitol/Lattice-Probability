import LatticeProb.LQG.RecentredSquareGeometric
import LatticeProb.LQG.RecentredSquareIncrementMoment

/-! # First moments of normalized recentred square increments -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open MatedCRTHarmonic.MoTPort QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- After normalization by the square of the scale, the expected absolute
increment of the same recentred process has a uniform geometric bound. -/
theorem lintegral_recentred_square_increment_le_geometric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) (m n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) * ENNReal.ofReal
      |(lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
        (radius (m + n) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal -
       (lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
        (radius (m + (n + 1)) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal| ∂P ≤
    ENNReal.ofReal (cRate γ 0 (1 / 4)) *
      ENNReal.ofReal (Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
        ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2))) ^ n := by
  let := hH.isProbabilityMeasure
  let ε : ℝ := 2 * radius m
  let S := sqQ (sqCorner z (radius m)) m
  let U := fun j w ω => H (radius j) w ω - H ε z ω
  have hε : 0 < ε := by dsimp [ε]; exact mul_pos (by norm_num) (radius_pos m)
  have hm : radius m ≤ ε / 2 := by dsimp [ε]; linarith
  have hS : ∀ t ∈ S, ‖t - z‖ ≤ ε / 2 := fun t ht =>
    (norm_sub_le_of_mem_centred_sqQ z m ht).trans hm
  have hSf : volume S < ⊤ := (centred_sqQ_volume_bounds z hm).1
  have hk (j : ℕ) : radius (m + j) ≤ ε / 2 :=
    (AreaExist.aradius_anti (Nat.le_add_right m j)).trans hm
  have hint (j : ℕ) : Integrable (fun ω =>
      (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
        (radius (m + j) / ε) S).toReal) P := by
    have heq (ω : Ω) : lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
        (radius (m + j) / ε) S = ConeArea6.massU γ S ε (m + j) U ω :=
      lqgApprox_rescale_recentred_eq_massU H ω γ z hε.ne' (m + j)
        (measurableSet_sqQ _ _)
    simp_rw [heq]
    exact ConeArea6.integrable_massU_toReal γ hε hSf
      (levelHyp_recentred_circle hH hHm hε z (hk j) hS)
  have hdiff : Integrable (fun ω =>
      |(lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
        (radius (m + n) / ε) S).toReal -
       (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
        (radius (m + (n + 1)) / ε) S).toReal|) P := by
    simpa only [Pi.sub_apply] using ((hint n).sub (hint (n + 1))).abs
  have hbound := integral_abs_recentred_square_increment_le_geometric hH hHm hγ hγ2 z m n
  change ∫⁻ ω, ENNReal.ofReal (ε⁻¹ ^ 2) * ENNReal.ofReal
    |(lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
        (radius (m + n) / ε) S).toReal -
     (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
        (radius (m + (n + 1)) / ε) S).toReal| ∂P ≤ _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hdiff (ae_of_all _ fun _ => abs_nonneg _)]
  calc
    _ ≤ ENNReal.ofReal (ε⁻¹ ^ 2) * ENNReal.ofReal
        (cRate γ 0 (1 / 4) * ε ^ 2 *
          Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
            ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2)) ^ n) := by
      apply mul_le_mul' le_rfl
      exact ENNReal.ofReal_le_ofReal (by simpa only [ε, S, Nat.add_assoc] using hbound)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_pow (Real.exp_pos _).le]
      rw [← ENNReal.ofReal_mul (cRate_nonneg (by norm_num))]
      congr 1
      field_simp [hε.ne']

end LatticeProb.LQG
