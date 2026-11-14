/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_source_radius_eq_ratio {K m : ℕ} (hmK : m ≤ K) :
    LaneCInputs.sourceRadius K m = (2 : ℝ) ^ m / (2 : ℝ) ^ K := by
  have hpowDiff : 0 < (2 : ℝ) ^ (K - m) := by positivity
  have hpowEq : (2 : ℝ) ^ K = (2 : ℝ) ^ m * (2 : ℝ) ^ (K - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmK]
  rw [LaneCInputs.sourceRadius, inv_pow, hpowEq]
  field_simp

 
private theorem laneC_thirtytwo_mul_le_two_pow (K : ℕ) (hK : 8 ≤ K) :
    (32 : ℝ) * K ≤ (2 : ℝ) ^ K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      have hk' : (8 : ℝ) ≤ k := by exact_mod_cast hk
      push_cast
      nlinarith

 

theorem laneC_source_outer_radius_lt_eighth
    {K m : ℕ} {ε : ℝ} (hK : 8 ≤ K) (hmK : m + 1 ≤ K)
    (hε : ε ≤ 1)
    (hm : (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ ε) :
    2 * LaneCInputs.sourceRadius K m < 1 / 8 := by
  have hmk : m ≤ K := by omega
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hKe : (K : ℝ) ^ ε ≤ K := by
    convert Real.rpow_le_rpow_of_exponent_le hKreal hε using 1 <;> norm_num
  have hpowm : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ ((m : ℝ) - 1) := by
    calc
      (2 : ℝ) ^ m = (2 : ℝ) ^ (((m : ℝ) - 1) + 1) := by
        simp only [sub_add_cancel, Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((m : ℝ) - 1) * (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add (by norm_num) _ _
      _ = 2 * (2 : ℝ) ^ ((m : ℝ) - 1) := by norm_num; ring
  have hmBound : (2 : ℝ) ^ m < 2 * K := by nlinarith
  have hKBound := laneC_thirtytwo_mul_le_two_pow K hK
  have hpowK : 0 < (2 : ℝ) ^ K := by positivity
  rw [laneC_source_radius_eq_ratio hmk]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hratio : (2 * (2 : ℝ) ^ m) / (2 : ℝ) ^ K < 1 / 8 :=
    (div_lt_iff₀ hpowK).2 (by nlinarith)
  simpa only [mul_div_assoc] using hratio

end SupercriticalLQGUniqueness.B2.DG20Conc
