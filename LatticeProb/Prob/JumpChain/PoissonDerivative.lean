import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiating a Poisson average at zero

A uniformly bounded sequence has an entire exponential generating function. Multiplying
by the exponential factor gives a Poisson average, whose derivative at zero is the
first increment of the sequence. The series here is defined for all real parameters.
-/

namespace LatticeProb.JumpChain

open scoped ENNReal NNReal

noncomputable section

/-- Bounded coefficients divided by factorials define a power series of infinite radius. -/
theorem radius_ofScalars_div_factorial (b : ℕ → ℝ) {C : ℝ}
    (hb : ∀ n, |b n| ≤ C) :
    (FormalMultilinearSeries.ofScalars ℝ (fun n ↦ b n / n.factorial)).radius = ∞ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  apply ((NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).summable.mul_left C).of_nonneg_of_le
  · intro n
    exact mul_nonneg (norm_nonneg _) (pow_nonneg r.property n)
  · intro n
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs, abs_div,
      Nat.abs_cast]
    calc
      |b n| / (n.factorial : ℝ) * (r : ℝ) ^ n ≤
          C / (n.factorial : ℝ) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (hb n) (Nat.cast_nonneg _)) (pow_nonneg r.property n)
      _ = C * ((r : ℝ) ^ n / (n.factorial : ℝ)) := by ring

/-- The exponential generating function of a bounded sequence has first derivative `b 1`. -/
theorem hasDerivAt_tsum_div_factorial (b : ℕ → ℝ) {C : ℝ}
    (hb : ∀ n, |b n| ≤ C) :
    HasDerivAt (fun x : ℝ ↦ ∑' n : ℕ, b n / n.factorial * x ^ n) (b 1) 0 := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun n ↦ b n / n.factorial)
  have hp : 0 < p.radius := by
    rw [radius_ofScalars_div_factorial b hb]
    exact ENNReal.zero_lt_top
  have h := (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt.hasDerivAt
  change HasDerivAt (FormalMultilinearSeries.ofScalarsSum (fun n ↦ b n / n.factorial))
    (p 1 fun _ ↦ 1) 0 at h
  simpa only [p, FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul,
    FormalMultilinearSeries.ofScalars_apply_eq, Nat.factorial_one, Nat.cast_one,
    div_one, one_pow, mul_one] using h

/-- The Poisson-weighted average of a bounded sequence has derivative `b 1 - b 0` at zero. -/
theorem hasDerivAt_poisson_average (b : ℕ → ℝ) {C : ℝ}
    (hb : ∀ n, |b n| ≤ C) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (-x) *
      ∑' n : ℕ, b n / n.factorial * x ^ n) (b 1 - b 0) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).neg.exp).fun_mul
    (hasDerivAt_tsum_div_factorial b hb)
  have hzero : (∑' n : ℕ, b n / n.factorial * (0 : ℝ) ^ n) = b 0 := by
    rw [tsum_eq_single 0]
    · simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
    · intro n hn
      rw [zero_pow hn, mul_zero]
  simpa only [Pi.neg_apply, id_eq, neg_zero, Real.exp_zero, neg_mul,
    one_mul, mul_one, hzero,
    neg_add_eq_sub] using h

end

end LatticeProb.JumpChain
