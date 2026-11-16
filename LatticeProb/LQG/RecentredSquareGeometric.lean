import LatticeProb.LQG.RecentredSquareL1

/-! # Geometric decay of recentred square increments -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- The geometric rate in the increment estimate is strictly between zero and one. -/
theorem recentred_square_increment_rate_mem (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
      ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2)) ∧
    Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
      ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2)) < 1 := by
  have hβ : 0 < min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
      ((2 - γ) ^ 2 / 4) := lt_min (areaRateExp_pos hγ hγ2) (by positivity)
  constructor
  · exact Real.exp_pos _
  · rw [← Real.exp_zero, Real.exp_lt_exp]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hβ) (mul_pos (by norm_num) hlog)

/-- At the square scale, the expected absolute increment decays geometrically
in the number of finer dyadic levels. -/
theorem integral_abs_recentred_square_increment_le_geometric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) (m n : ℕ) :
    ∫ ω, |(lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + n) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal -
        (lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
          (radius (m + n + 1) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)).toReal| ∂P ≤
      cRate γ 0 (1 / 4) * (2 * radius m) ^ 2 *
        Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
          ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2)) ^ n := by
  have hr : 0 < radius m := radius_pos m
  have hε : 0 < 2 * radius m := by positivity
  have hm : radius m ≤ (2 * radius m) / 2 := by linarith
  have hbound := integral_abs_recentred_square_increment_le hH hHm hγ hγ2 hε z hm
    (Nat.le_add_right m n)
  refine hbound.trans ?_
  have hβ : 0 ≤ min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
      ((2 - γ) ^ 2 / 4) := le_min (areaRateExp_pos hγ hγ2).le (by positivity)
  have hlog : 0 ≤ Real.log ((2 * radius m) / radius m) :=
    Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hLi : (n : ℝ) * (1 / 2 * Real.log 2) ≤
      1 / 2 * Real.log ((2 * radius m) / radius (m + n)) := by
    have hrad : radius (m + n) = radius m * (2 : ℝ)⁻¹ ^ n := by
      simp only [radius, pow_add]
    rw [hrad, ← div_div, Real.log_div (div_pos hε hr).ne'
      (pow_pos (by norm_num) n).ne', Real.log_pow, Real.log_inv]
    linarith
  have hC : 0 ≤ cRate γ 0 (1 / 4) * (2 * radius m) ^ 2 :=
    mul_nonneg (cRate_nonneg (by norm_num)) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left hLi hβ
  linarith

end LatticeProb.LQG
