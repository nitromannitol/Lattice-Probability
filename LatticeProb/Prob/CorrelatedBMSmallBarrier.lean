import LatticeProb.Prob.CorrelatedBMJointWindowTransfer

/-! # Extending a small-barrier probability estimate -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A uniform power bound for small positive barriers extends to every positive
barrier, after increasing the constant to at least one. -/
theorem measure_jointZeroBarrier_le_of_small_barrier {γ : ℝ} (B p : ℝ)
    (hp : 0 ≤ p)
    (hsmall : ∀ (q : ℝ), 0 < q → q < 1 → ∀ ν : Measure Path2,
      IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier q 1) ≤ ENNReal.ofReal (B * q ^ p)) :
    ∀ (q : ℝ), 0 < q → ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν →
      ν (jointZeroBarrier q 1) ≤ ENNReal.ofReal (max B 1 * q ^ p) := by
  intro q hq ν hν
  by_cases hq1 : q < 1
  · exact (hsmall q hq hq1 ν hν).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left B 1)
        (Real.rpow_nonneg hq.le p)))
  · have : IsProbabilityMeasure ν := hν.isProbabilityMeasure
    have hpow : 1 ≤ q ^ p := Real.one_le_rpow (le_of_not_gt hq1) hp
    have hreal : 1 ≤ max B 1 * q ^ p := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ max B 1 * q ^ p := mul_le_mul (le_max_right B 1) hpow (by norm_num)
          (by linarith [le_max_right B 1])
    calc
      ν (jointZeroBarrier q 1) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal (max B 1 * q ^ p) := ENNReal.ofReal_le_ofReal hreal

end LatticeProb.CorrelatedBM
