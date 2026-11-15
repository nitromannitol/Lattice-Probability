import LatticeProb.Prob.CorrelatedBMForwardClosedBound

/-! # Correlation angles and forward Brownian barriers -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The whitening coefficients are the half-angle sine and cosine. -/
theorem whitening_coefficients_eq_half_angle {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 =
        Real.sin ((Real.pi * γ ^ 2 / 4) / 2) ∧
    Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2 =
        Real.cos ((Real.pi * γ ^ 2 / 4) / 2) := by
  let θ := Real.pi * γ ^ 2 / 4
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    nlinarith [mul_lt_mul_of_pos_left hγsq Real.pi_pos]
  have hsin : 0 ≤ Real.sin (θ / 2) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
  have hcos : 0 ≤ Real.cos (θ / 2) :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩).le
  have hsin2 := Real.sin_sq_eq_half_sub (θ / 2)
  have hcos2 := Real.cos_sq (θ / 2)
  have hdouble : 2 * (θ / 2) = θ := by ring
  rw [hdouble] at hsin2 hcos2
  have hρ : lrCov γ 0 1 = -Real.cos θ := rfl
  have hrad1 : 0 ≤ 2 * (1 + lrCov γ 0 1) := by
    rw [hρ]; nlinarith [Real.cos_le_one θ]
  have hrad2 : 0 ≤ 2 * (1 - lrCov γ 0 1) := by
    rw [hρ]; nlinarith [Real.neg_one_le_cos θ]
  have hsqrt1 := Real.sq_sqrt hrad1
  have hsqrt2 := Real.sq_sqrt hrad2
  have hsqrt1pos := Real.sqrt_nonneg (2 * (1 + lrCov γ 0 1))
  have hsqrt2pos := Real.sqrt_nonneg (2 * (1 - lrCov γ 0 1))
  rw [hρ] at hsqrt1 hsqrt2 hsqrt1pos hsqrt2pos
  constructor
  · change Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 = Real.sin (θ / 2)
    rw [hρ]
    nlinarith
  · change Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2 = Real.cos (θ / 2)
    rw [hρ]
    nlinarith

/-- A uniform forward closed-barrier estimate for every subcritical exponent. -/
theorem jointZeroBarrier_le_subcritical {γ r : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hr : 0 < r) (hrγ : r < 4 / γ ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {μ : Measure Path2}, IsCorrelatedBM2 γ μ →
      ∀ (q : ℝ) (T : ℝ≥0), 0 < q → 0 < (T : ℝ) →
        μ (jointZeroBarrier q T) ≤ ENNReal.ofReal
          (K * (((2 * q) / (Real.sin ((Real.pi * γ ^ 2 / 4) / 2) * Real.sqrt 2)) /
            Real.sqrt (T : ℝ)) ^ r) := by
  have hγsq0 : 0 < γ ^ 2 := sq_pos_of_pos hγ0
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by positivity
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hγsq Real.pi_pos]
  obtain ⟨p, hrp, hp⟩ := exists_between hrγ
  have hpγ : p * γ ^ 2 < 4 := (lt_div_iff₀ hγsq0).mp hp
  have hpθ : p * (Real.pi * γ ^ 2 / 4) < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hpγ Real.pi_pos]
  obtain ⟨ha, hb⟩ := whitening_coefficients_eq_half_angle hγ0 hγ2
  exact jointZeroBarrier_le_of_wedge_angle hγ0 hγ2 hθ0 hθπ hr hrp hpθ ha hb

end LatticeProb.CorrelatedBM
