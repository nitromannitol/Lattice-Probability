/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseIndexRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBScaleCutoff
import Mathlib.Data.Nat.Choose.Bounds

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneB_coarseIndex_add_one_le (Q : PsiParams) (K : ℕ)
    (hε : Q.ε₀ ≤ 1) (hK : 2 ≤ K) :
    laneBCoarseIndex Q K + 1 ≤ K := by
  have hpow : K ≤ 2 ^ (K - 1) := by
    have h := Nat.choose_succ_le_two_pow (K - 1) 1
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ K)] using h
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hle : (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ ((K - 1 : ℕ) : ℝ) := by
    calc
      (K : ℝ) ^ Q.ε₀ ≤ K := Real.rpow_le_self_of_one_le hKreal hε
      _ ≤ (2 : ℝ) ^ (K - 1 : ℕ) := by exact_mod_cast hpow
      _ = (2 : ℝ) ^ ((K - 1 : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
  have hm : laneBCoarseIndex Q K ≤ K - 1 := by
    apply Nat.ceil_le.mpr
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (Real.rpow_pos_of_pos hKpos _)).mpr hle
  omega

end SupercriticalLQGUniqueness.B2.DG20Conc
