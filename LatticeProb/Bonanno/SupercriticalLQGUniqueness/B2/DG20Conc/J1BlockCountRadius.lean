/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockCountRadius at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearIdx

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_thirtytwo_k_four_pow_le_five_pow (K : ℕ) (hK : 64 ≤ K) :
    32 * K * 4^K ≤ 5^K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
      have hs : 4 * (K + 1) ≤ 5 * K := by omega
      calc
        32 * (K + 1) * 4^(K + 1) =
            (4 * (K + 1)) * (32 * 4^K) := by ring
        _ ≤ (5 * K) * (32 * 4^K) := Nat.mul_le_mul_right _ hs
        _ = 5 * (32 * K * 4^K) := by ring
        _ ≤ 5 * 5^K := Nat.mul_le_mul_left _ ih
        _ = 5^(K + 1) := by ring

theorem j1_nearIdx_card_radius_le_five
    (K : ℕ) (hK : 64 ≤ K) (R : ℝ)
    (hR0 : 0 ≤ R) (hRK : R ≤ 2 * (K : ℝ)) :
    (T20B.nearIdx K).card * R ≤ (5 : ℝ)^K := by
  have hc : ((T20B.nearIdx K).card : ℝ) ≤ 16 * (4 : ℝ)^K := by
    exact_mod_cast j1_nearIdx_card_le_four K
  have hp : 16 * (4 : ℝ)^K * (2 * (K : ℝ)) ≤ (5 : ℝ)^K := by
    have hn := j1_thirtytwo_k_four_pow_le_five_pow K hK
    have hn' : (32 * K * 4^K : ℝ) ≤ (5^K : ℕ) := by exact_mod_cast hn
    convert hn' using 1 <;> push_cast <;> ring
  calc
    (T20B.nearIdx K).card * R ≤
        (16 * (4 : ℝ)^K) * R :=
          mul_le_mul_of_nonneg_right hc hR0
    _ ≤ (16 * (4 : ℝ)^K) * (2 * (K : ℝ)) := by gcongr
    _ ≤ (5 : ℝ)^K := hp

end SupercriticalLQGUniqueness.B2.DG20Conc
