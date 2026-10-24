import LatticeProb.Graph.LongRangeKernel.CriticalAsymptotics
import LatticeProb.Graph.LongRangeKernel.Lattice

/-!
# Volume at the critical inverse scale

The explicit critical inverse gives the logarithmic volume profile, uniformly down to time zero.
-/

namespace LatticeProb.Graph.LongRangeKernel

/-- The lattice volume at the critical inverse has the critical logarithmic profile. -/
theorem latticeVolume_criticalInverse_comparison (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      c * (1 + t * Real.log (2 + t)) ^ ((d : ℝ) / 2) ≤
        latticeVolumeProfile d (criticalInverse t) ∧
      latticeVolumeProfile d (criticalInverse t) ≤
        C * (1 + t * Real.log (2 + t)) ^ ((d : ℝ) / 2) := by
  refine ⟨(1 / 2 : ℝ) ^ d, (4 : ℝ) ^ d, by positivity, by positivity, ?_⟩
  intro t ht
  have hl : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + t) ≤ t * Real.log (2 + t) + 2 := by
    by_cases ht1 : t ≤ 1
    · have hb := Real.log_le_sub_one_of_pos (show 0 < 2 + t by linarith)
      have hp := mul_nonneg ht hl
      linarith
    · have hp := mul_le_mul_of_nonneg_right (le_of_not_ge ht1) hl
      linarith
  set q := 1 + t * Real.log (2 + t) with hq
  set s := Real.sqrt ((t + 2) * Real.log (t + 2) / 2) with hs
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (t + 2) * Real.log (2 + t) / 2 := by
    rw [hs, add_comm t 2, Real.sq_sqrt (by positivity)]
  have hr0 := Real.sqrt_nonneg q
  have hr2 := Real.sq_sqrt hq0
  have hsq : s ^ 2 ≤ 2 * q := by
    rw [hs2, hq]
    nlinarith [mul_nonneg ht hl]
  have hlow : (1 / 2 : ℝ) * Real.sqrt q ≤ 2 + s := by
    have hbase : q ≤ 2 * (2 + s) ^ 2 := by
      rw [hq]
      nlinarith [mul_nonneg ht hl]
    nlinarith [sq_nonneg (Real.sqrt q - 2 * (2 + s))]
  have hupp : 2 + s ≤ 4 * Real.sqrt q := by
    have hq1 : 1 ≤ q := by
      rw [hq]
      exact le_add_of_nonneg_right (mul_nonneg ht hl)
    have hbase : (2 + s) ^ 2 ≤ 12 * q := by
      nlinarith [sq_nonneg (s - 2)]
    nlinarith [sq_nonneg (2 + s - 4 * Real.sqrt q)]
  have hpower : (Real.sqrt q) ^ d = q ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
    congr 1
    ring
  have hlower := pow_le_pow_left₀ (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.sqrt q)
    hlow d
  have hupper := pow_le_pow_left₀ (by positivity : 0 ≤ 2 + s) hupp d
  rw [mul_pow, hpower] at hlower hupper
  change (1 / 2 : ℝ) ^ d * q ^ ((d : ℝ) / 2) ≤ (1 + criticalInverse t) ^ d ∧
    (1 + criticalInverse t) ^ d ≤ 4 ^ d * q ^ ((d : ℝ) / 2)
  have hz : 1 + criticalInverse t = 2 + s := by rw [criticalInverse, ← hs]; ring
  rw [hz]
  exact ⟨hlower, hupper⟩

end LatticeProb.Graph.LongRangeKernel
