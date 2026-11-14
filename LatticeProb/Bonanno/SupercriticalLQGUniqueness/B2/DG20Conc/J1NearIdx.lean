/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1NearIdx at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ThresholdExp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BBlocks
import Mathlib.Data.Int.Interval

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

theorem j1_nearIdx_card (K : ℕ) :
    (T20B.nearIdx K).card = (3 * 2^K + 1)^2 := by
  simp only [T20B.nearIdx, Finset.card_product, Int.card_Icc]
  have hp : (2 : ℤ) ^ (K + 1) + 1 + (2 : ℤ) ^ K =
      ((3 * 2^K + 1 : ℕ) : ℤ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [sub_neg_eq_add, hp, Int.toNat_natCast]
  ring

theorem j1_nearIdx_card_le_four (K : ℕ) :
    (T20B.nearIdx K).card ≤ 16 * 4^K := by
  rw [j1_nearIdx_card]
  have hpow : 1 ≤ 2^K := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hbase : 3 * 2^K + 1 ≤ 4 * 2^K := by omega
  have h4 : (4 : ℕ)^K = (2^K)^2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    ring
  calc
    (3 * 2^K + 1)^2 ≤ (4 * 2^K)^2 := by gcongr
    _ = 16 * 4^K := by
      rw [h4]
      ring

theorem j1_sixteen_four_pow_le_five_pow {K : ℕ} (hK : 16 ≤ K) :
    16 * 4^K ≤ 5^K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ, pow_succ]
      omega

theorem j1_nearIdx_card_le_five (K : ℕ) (hK : 16 ≤ K) :
    (T20B.nearIdx K).card ≤ 5^K :=
  (j1_nearIdx_card_le_four K).trans (j1_sixteen_four_pow_le_five_pow hK)

end SupercriticalLQGUniqueness.B2.DG20Conc
